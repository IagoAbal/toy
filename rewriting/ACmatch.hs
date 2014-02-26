{-# OPTIONS_GHC -funbox-strict-fields #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- | AC matching implementation based on Steven Eker's paper
-- /Associative-Commutative Matching via Bipartite Graph Matching/.
--
-- NB: Many of the source code comments are quotations from the
-- reference paper.

module ACmatch where

import Control.Applicative ( (<$>) )
import Control.Arrow ( second )
import Control.Exception ( assert )
import Control.Monad ( MonadPlus(..), foldM, forM, guard, when )
import Data.Function ( on )
import Data.Function.Predicate ( equals, is, isn't )
import Data.List
  ( intercalate, minimum, nub )
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Maybe ( fromJust, fromMaybe, isJust, listToMaybe, mapMaybe )
import Data.Monoid ( Monoid(..) )
import Data.Set ( Set )
import qualified Data.Set as Set

import Math.Combinat.Compositions ( allCompositions' )

-- import Debug.Trace ( trace )

-- * Terms

type Name = String

  -- | Pre-terms, when /not/ in ONF.
  -- i.e. no 'ACapp' terms.
type Term' = Term

data Term = Var { varName :: !Name }
            -- ^ Variables
          | Const !Name
            -- ^ Constant symbols, i.e. 0-arity functions
          | App !Fun [Term]
            -- ^ Regular (non AC) functions (when in ONF)
          | ACapp !Fun TermMuls
            -- ^ AC functions
            -- Arguments are represented as permutations
    deriving(Eq,Ord)

type VarTm = Term     -- ^ Variable term
type Pattern = Term
type Subject = Term

instance Show Term where
  show (Var x)   = x
  show (Const a) = a
  show (App f ts)
    = show f ++ "(" ++ intercalate "," (map show ts) ++ ")"
  show (ACapp f ts)
    = show f ++ "*(" ++ intercalate "," (map show $ elemsTM ts) ++ ")"

isVar (Var _) = True
isVar _other  = False

isConst (Const _) = True
isConst _other  = False

isApp (App _ _) = True
isApp (ACapp _ _) = True
isApp _other  = False

topSymbol (App f _) = f
topSymbol (ACapp f _) = f

  -- | An efficient alternative to @Set.map topSymbol@.
  -- Complexity is /O(n)/ instead of /O(n*log n)/.
  -- This works because 'topSymbol' is monotonic, even though it doesn't
  -- fulfill the stricter monotonicity required by 'Set.mapMonotonic'.
  -- pre: All terms in input are App-terms.
getTopSymbols :: Set Term -> Set Fun
getTopSymbols = Set.fromAscList . map topSymbol . Set.toAscList


-- * Function symbols

data Fun = Free !Pos  -- ^ Arity.
                !Name
         | ACfn !Name
            -- ^ AC function (2-arity).
    deriving(Eq,Ord)

instance Show Fun where
  show (Free _ f) = f
  show (ACfn f) = f

isFree :: Fun -> Bool
isFree (Free _ _) = True
isFree _other     = False

isAC :: Fun -> Bool
isAC (ACfn _) = True
isAC _other   = False

-- * Matching

match :: Pattern -> Subject -> [Bindings]
match p s
  = case buildHierarchy (onf p) (onf s) mempty of
        Nothing -> []
        Just h  -> do GHSolution bs sp <- solveHierarchy h mempty
                      bs1 <- case substSemipures bs sp of
                                 Nothing -> []
                                 Just sp1 -> solveSemipureSystem $
                                                buildSemipureSystem sp1
                      return $ bs `mappend` bs1

-- * Ordered Normal Form
--
-- A term /t/ which contains AC functions is a representative of a
-- congruence class of terms which are equal modulo
-- associativity-commutativity. The /ordered normal form/ (ONF) gives
-- us a canonical representative for each such congruence class, so by
-- converting terms to ONF we can check for equality modulo AC by
-- checking for syntactic equality.
--
-- NB: We resort to the total order defined by automatically by our
-- Haskell compiler when /deriving/ the 'Ord' /type class/. The exact
-- order is not important as long as you define one.
--
-- NB: Also note that our 'onf' function does a single pass, note that
-- we do not represent arguments of an AC function as linked-lists but
-- as maps, so this is the most natural (and efficient?) way.
--

onf :: Term' -> Term
onf (Var x) = Var x
onf (Const a) = Const a
onf (App f ts) | isFree f = App f $ map onf ts
onf (App f [t1,t2]) | isAC f = ACapp f $ go t1 `mappend` go t2
  where go (onf -> ACapp f1 ts)
            | f1 == f = ts
        go t          = singleTM t 1


-- * Hierarchy of Bipartite Graphs
-- The AC matching problem is decomposed into smaller AC matching
-- subproblems.

  -- | If the pattern has a non-AC top symbol then, as a result of
  -- matching, we either have a failure or (possibly empty) sets of
  -- bindings and AC matching subproblems.
  -- If instead the top symbol of the pattern is an AC function then
  -- we have an empty set of variable bindings and a set of AC
  -- subproblems that has the whole problem as its single member.
data GraphHierarchy
  = GraphHierarchy {
      gh_ac_subproblems :: ACSubproblems
        -- ^ AC matching subproblems.
    , gh_bindings :: Bindings
        -- ^ Variables already assigned.
    }
    deriving Show

instance Monoid GraphHierarchy where
  mempty = GraphHierarchy [] mempty
  mappend (GraphHierarchy ac1 bs1) (GraphHierarchy ac2 bs2)
    = GraphHierarchy (ac1 ++ ac2) (bs1 `mappend` bs2)

type ACSubproblems = [ACSubproblem]

data ACSubproblem
  = ACSubproblem {
      ac_top_symbol :: Fun
        -- ^ AC top symbol.
    , ac_variables :: VarTmMuls
        -- ^ Pattern variables.
    , ac_leftovers :: TermMuls
        -- ^ Unmatched subject terms.
        -- These have to be assigned to some variable.
    , ac_graphs :: BipartiteGraphs
        -- ^ For every function symbol (AC or free) occurring directly
        -- bellow the top symbol of the AC subproblem we form a
        -- bipartite graph.
    }
    deriving Show

type BipartiteGraphs = [BipartiteGraph]

  -- | A bipartite graph for a function symbol /f/ represents all
  -- possible matchings for the f-subpatterns of the enclosing
  -- AC subproblem.
data BipartiteGraph
  = BipartiteGraph {
     bg_top_symbol :: Fun
        -- ^ Function symbol (AC or free).
   , bg_pattern_nodes :: PatternNodes
        -- ^ Pattern subterms.
   , bg_subject_nodes :: TermMuls
        -- ^ Subject subterms.
  }
  deriving Show

type PatternNodes = [PatternNode]

data PatternNode
  = PatNode {
      pn_term  :: Pattern
    , pn_mult  :: !Pos
    , pn_edges :: Edges
        -- ^ Possible matchings with the subject nodes.
    }
    deriving Show

type Edges = [Edge]

data Edge
  = Edge {
      e_subject :: Subject
        -- ^ An element of the set of subject nodes of the
        -- enclosing bipartite graph.
    , e_consequences :: GraphHierarchy
        -- ^ As a consequence of matching a pattern subterm with a
        -- subject subterm we get another graph hierarchy.
    }
    deriving Show


  -- simplify performs trivial matches and builds a single level
  -- in the graph hierarchy.
simplify :: Pattern -> Subject -> Bindings -> Maybe GraphHierarchy

simplify (Var x) t bs
  | Just t1 <- lookupB x bs
  , t1 /= t   = fail "variable clash"
  | otherwise = return $ GraphHierarchy [] (x *:= t)
  
simplify (Const a) (Const b) _bs
  | a == b = return $ GraphHierarchy [] mempty

  -- For free functions we proceed in the usual way.
  -- NB: We assume well-typed terms so we know that length ps == length ss
simplify (App f ps) (App f1 ss) bs'
  | f == f1 = foldM goArg (GraphHierarchy [] bs') (zip ps ss)
  where goArg h (p,s) = mappend h <$> simplify p s (gh_bindings h)

simplify (ACapp f ps) (ACapp f1 ss) _bs
  | f == f1 = do
      -- eliminate pattern constants
      -- pre: all pattern constants must appear in the subject
    ss1 <- (ss `subTM` ps_a) `pre` (ps_a `isSubTMOf` ss)
    let (ss_a, ss_fx) = partitionTM (const . isConst) ss1
          -- collect left over subject terms
          -- i.e. remaining constants + functions not appearing in the pattern
        _L = ss_a `mappend`
              filterTM (\t _ -> topSymbol t `Set.notMember` ps_fs) ss_fx
    return $ GraphHierarchy [ACSubproblem f _V _L _G] mempty
  where _V = getVarsTM ps      -- collect pattern variables
        ps_a = getConstsTM ps  -- pattern constants
        ps_apps = getAppsTM ps
        ps_fs = getTopSymbols $ termSetTM ps_apps
        _G = [ BipartiteGraph f _P _S       -- bipartite graphs with no edges
             | f <- Set.toList ps_fs
             , let _P = [ PatNode t n []    -- pattern nodes (no edges yet)
                        | TM t n <- elemsTM $ getFunTM f ps_apps
                        ]
             , let _S = getFunTM f ss       -- subject nodes
             ]

simplify _p _s _bs = fail "do not match"


  -- | Decompose the matching problem into a hierarchy of bipartite
  -- graphs together with ancillary data.
buildHierarchy :: Pattern -> Subject -> Bindings -> Maybe GraphHierarchy
buildHierarchy t u bs = do
  GraphHierarchy{gh_ac_subproblems,gh_bindings} <- simplify t u bs
  let bs' = bs `mappend` gh_bindings
  _A' <- forM gh_ac_subproblems $ \(ACSubproblem _F _V _L _G) -> do
    _G' <- forM _G $ \(BipartiteGraph f _P _S) -> do
      _P' <- forM _P $ \(PatNode p m _) -> do
              -- builds an edge for each subject that is matchable with
              -- the pattern /p/.
        let mkEdge (TM s _) = Edge s <$> buildHierarchy p s bs'
            _E = mapMaybe mkEdge $ filter ((>=m) . tm_mult) $ elemsTM _S
        when (null _E) $ fail "unmatchable pattern"
        return $ PatNode p m _E   -- fill the edge set
      return $ BipartiteGraph f _P' _S
    return $ ACSubproblem _F _V _L _G'
      -- for efficiency the graph hierarchy only stores the variable
      -- bindings found by simplify that are distinct from those it
      -- was passed in its arguments.
  return $ GraphHierarchy _A' (gh_bindings `subB` bs)


-- * Graph Hierarchy Solution
-- We define a /local solution/ of a bipartite graph problem
-- g = (f,P,S) as a /valid/ (see the paper) assignment of a subject
-- node from S to each pattern node in P.
-- We define the solution of a graph hierarchy to be a local solution
-- of each of its bipartite graph problems together with solutions
-- of all the graph hierarchies in the consequence set of each of these
-- local solutions.

type GHSolutions = [GHSolution]

  -- | Solution of a graph hierarchy.
data GHSolution
  = GHSolution {
    ghs_bindings :: Bindings
  , ghs_semipure :: Semipures
      -- ^ Semi-pure AC problems.
  }
  deriving Show

instance Monoid GHSolution where
  mempty = GHSolution mempty mempty
  mappend (GHSolution bs1 sp1) (GHSolution bs2 sp2)
      = GHSolution (bs1 `mappend` bs2) (sp1++sp2)

ghsPlusB :: GHSolution -> Bindings -> GHSolution
ghsPlusB (GHSolution bs sp) bs1
  = GHSolution (bs1 `mappend` bs) sp

type Semipures = [Semipure]

  -- | Semi-pure problem
  -- We call a AC matching problem semi-pure if the pattern consists of
  -- a single AC function symbol with only variable symbol arguments.
data Semipure
  = Semipure {
    sp_top_symbol :: !Fun
  , sp_lhs :: VarTmMuls
  , sp_rhs :: TermMuls
  }
  deriving Show

  -- TODO: Re-check substSemipure in the paper
substSemipure :: Bindings -> Semipure -> Maybe Semipure
substSemipure bs (Semipure f lhs rhs) = Semipure f lhs <$> rhs'
  where rhs' = foldTM mk_sub (Just rhs) lhs
        mk_sub _ _ Nothing     = Nothing
        mk_sub x n (Just rhs1) =
          case lookupB (varName x) bs of
              Nothing -> Just rhs1
              Just t  -> rmTM (TM t n) rhs1 `pre` (t `inTM` rhs1)

substSemipures :: Bindings -> Semipures -> Maybe Semipures
substSemipures bs = mapM (substSemipure bs)


  -- | Provide solutions for a graph hierarchy from a solution
  -- for the upper levels of the enclosing hierarchy.
solveHierarchy :: GraphHierarchy -> GHSolution -> GHSolutions

solveHierarchy GraphHierarchy{gh_ac_subproblems,gh_bindings}
               s@(GHSolution{ghs_bindings})
      -- a conflict between variable bindings makes solution inconsistent
  | gh_bindings `clashesWith` ghs_bindings = []
  | otherwise = solveACSubproblems gh_ac_subproblems s'
  where s' = ghsPlusB s gh_bindings

solveACSubproblems :: [ACSubproblem] -> GHSolution -> GHSolutions
solveACSubproblems []     s = [s]
solveACSubproblems (a:as) s = solveACSubproblem a s >>= solveACSubproblems as

  -- | Provide solutions for an AC subproblem, where each solution
  -- contains a new semi-pure AC equation.
solveACSubproblem :: ACSubproblem -> GHSolution -> GHSolutions
solveACSubproblem ACSubproblem{ac_top_symbol,ac_variables,ac_leftovers,ac_graphs} s
  = [ GHSolution bs (sp:sps)
    | (GHSolution bs sps,unused) <- solveBipartiteGraphs ac_graphs s
    , let sp = Semipure ac_top_symbol
                        ac_variables
                        (ac_leftovers `mappend` unused)
    ]

solveBipartiteGraphs :: BipartiteGraphs -> GHSolution -> [(GHSolution,TermMuls)]
solveBipartiteGraphs []     s = [(s,mempty)]
solveBipartiteGraphs (g:gs) s = do
  (s1,unused) <- solveBipartiteGraph g s
  map (second (unused `mappend`)) $   -- collect unused subject terms
      solveBipartiteGraphs gs s1

  -- | Provide solutions for a bipartite graph problem by picking
  -- the allowed combinations of edges.
solveBipartiteGraph :: BipartiteGraph -> GHSolution -> [(GHSolution,TermMuls)]
solveBipartiteGraph BipartiteGraph{bg_pattern_nodes,bg_subject_nodes} s
  = goPatterns bg_pattern_nodes bg_subject_nodes s

goPatterns :: [PatternNode] -> TermMuls -> GHSolution -> [(GHSolution,TermMuls)]
goPatterns []       sns s = [(s,sns)]
goPatterns (pn:pns) sns s = do
  (s1,sns1) <- goPattern pn sns s
  goPatterns pns sns1 s1

  -- | Pick an edge and returns possible solutions together with the
  -- new set of available subject terms.
goPattern :: PatternNode -> TermMuls -> GHSolution -> [(GHSolution,TermMuls)]
goPattern PatNode{pn_term,pn_mult,pn_edges} sns s = pn_edges >>= goEdge
  where goEdge :: Edge -> [(GHSolution,TermMuls)]
        goEdge Edge{e_subject,e_consequences}
          | Just m <- lookupTM e_subject sns
          , m >= pn_mult
          , let ss1 = solveHierarchy e_consequences s
          , not $ null ss1    -- consequences must be consistent
          , let sns1 = rmTM (TM e_subject pn_mult) sns 
          = map (,sns1) ss1
          | otherwise = []


-- * Solving Semi-pure Systems

data SemipureSystem
  = SemipureSystem {
     sps_variables :: VarRecords
   , sps_terms     :: TermRecords
   , sps_equations :: EqRecords
  }
  deriving Show

type VarRecords = [VarRecord]

data VarRecord
  = Shared {
     v_var :: !VarTm
  }   -- ^ A variable that occurs under more than one AC symbol.    
  | Owned {
     v_var :: !VarTm
   , v_owner :: !Fun  -- ^ AC symbol owning the variable.
  }   -- ^ A variable that occurs under just one AC symbol.

instance Show VarRecord where
  show (Shared x) = show x
  show (Owned x f) = show x ++ '_' : show f

new_shared :: VarTm -> VarRecord
new_shared v = Shared v

new_owned :: VarTm -> Fun -> VarRecord
new_owned v f = Owned v f

type TermRecords = [TermRecord]

data TermRecord
  = TmRec {
     t_term     :: Term
   , t_subterms :: TermMuls
      -- ^ Only used if all the subterms of /t_term/ are in the RHS of
      -- a semipure equation headed by /top_symbol(t_term)/.
      -- Otherwise it is empty.
  }

instance Show TermRecord where
  show (TmRec t us) | nullTM us = show t
                    | otherwise = '@' : show t

type EqRecords = [EqRecord]

data EqRecord
  = EqRec {
     eq_top_symbol :: !Fun
   , eq_var_mult :: VarTmMuls
   , eq_term_mult :: TermMuls
  }

instance Show EqRecord where
  show (EqRec f vs ts)
    = show (ACapp f vs) ++ " ==? " ++ show (ACapp f ts)

lookupTI :: Term -> TermMuls -> Pos
lookupTI t = fromMaybe 0 . lookupTM t

  -- TODO: Improve efficiency (there is lot of room for improvement...)
  -- E.g. vrs can be build incrementally in O(n*log n) steps
buildSemipureSystem :: Semipures -> SemipureSystem
buildSemipureSystem [] = SemipureSystem [] [] []
buildSemipureSystem sps = SemipureSystem vrs trs eqs
  where sys_vars = Set.toList $ Set.unions $ map (termSetTM . sp_lhs) sps
        sys_terms = Set.toList $ Set.unions $ map (termSetTM . sp_rhs) sps
        isOwned v
          | length sp_v == 1 = listToMaybe sp_v
          | otherwise        = Nothing
          where sp_v = nub $ [ f | Semipure f lhs _ <- sps
                                 , v `inTM` lhs
                             ]
        mk_var_record v
          | Just f <- isOwned v = new_owned v f
          | otherwise           = new_shared v
        vrs = map mk_var_record sys_vars
        trs = [ TmRec t (mk_subterms t)
              | t <- sys_terms
              ]
        mk_subterms (ACapp f ts)
          | any (sp_rhs `is` (ts `isSubTMOf`)) sps = ts
        mk_subterms t = mempty
        eqs = [ EqRec f lhs rhs
              | Semipure f lhs rhs <- sps
              ]


solveSemipureSystem :: SemipureSystem -> [Bindings]
solveSemipureSystem (SemipureSystem _V _T _E) = goVars _V _E
  where goVars :: VarRecords -> EqRecords -> [Bindings]
        goVars []     _E1
          = do guard (null _E1)
               return mempty
        goVars (v:vs) _E1 = do
            (b,eqs) <- goVar v _T _E1
            bs <- goVars vs eqs
            return (insertB b bs)

goVar (Shared x) _T _E2  = goShared x _T _E2
goVar (Owned x f) _T _E2 = goOwned f x _T _E2


goShared :: VarTm -> TermRecords -> EqRecords -> [(Binding,EqRecords)]
goShared x _T _E = _T >>= go_term
  where go_term :: MonadPlus m => TermRecord -> m (Binding,EqRecords)
        go_term t@(TmRec{t_term,t_subterms})
          = do _E' <- mapM go_eq _E
               return (varName x := t_term,filter (not . nullTM . eq_term_mult) _E')
          where go_eq :: MonadPlus m => EqRecord -> m EqRecord
                go_eq e@(EqRec{eq_top_symbol,eq_var_mult,eq_term_mult})
                    | vm > 0
                    , Just f <- topSymbol t_term `pre` isApp t_term
                    , f == eq_top_symbol
                    = if nullTM t_subterms ||
                          (any (\(TM u m) -> lookupTI u eq_term_mult < m*vm) $ elemsTM t_subterms)
                        then mzero
                        else return e{ eq_var_mult = deleteTM x eq_var_mult
                                     , eq_term_mult = eq_term_mult
                                                    `subTM` mapTM (*vm) t_subterms
                                     }
                    | vm > 0 && tm >= vm
                    = return e{ eq_var_mult = deleteTM x eq_var_mult
                              , eq_term_mult = rmTM (TM t_term vm) eq_term_mult
                              }
                    | otherwise
                    = mzero
                  where vm = lookupTI x eq_var_mult
                        tm = lookupTI t_term eq_term_mult

goOwned :: Fun -> VarTm -> TermRecords -> EqRecords -> [(Binding,EqRecords)]
goOwned f x _T _E = map mkSol comps
  where max_assign =  [ minimum [ m `div` vm
                                | EqRec{eq_var_mult,eq_term_mult} <- _E
                                , let vm = lookupTI x eq_var_mult
                                      m = lookupTI t eq_term_mult
                                , vm > 0
                                ]
                      | TmRec t _ <- _T
                      ]
        (_T',max_assign') = unzip $ filter ((>0) . snd) $ zip _T max_assign
        ts = map t_term _T'
        comps = concat $ tail $ allCompositions' max_assign'
        -- TODO: go_eq :: MonadPlus m => EqRecord -> m EqRecord
        -- If an equation has no variable in its lhs but still terms in
        -- its rhs then we return mzero... hence discarding the solution.
        mkSol :: [Int] -> (Binding,EqRecords)
        mkSol ks = (b,_E')
            where b = varName x := mk_x_tm
                  mk_x_tm | [t] <- ts'
                          , [1] <- ks'
                          = t
                          | otherwise
                          = ACapp f $ mkTermMuls $ zip ts' ks'
                  (ts',ks') = unzip $ filter ((>0) . snd) $ zip ts ks
                  _E' = [ e{ eq_var_mult = deleteTM x eq_var_mult
                           , eq_term_mult = eq_term_mult'
                           }
                        | e@(EqRec{eq_var_mult,eq_term_mult}) <- _E
                        , let vm = lookupTI x eq_var_mult
                        , vm > 0
                        , let tks = mkTermMuls $ zipWith (\t -> (t,) . (*vm)) ts' ks'
                              eq_term_mult' = eq_term_mult `subTM` tks
                        , not (nullTM eq_term_mult')
                        ]
                        ++ filter (\e -> lookupTI x (eq_var_mult e) == 0) _E

-- * Term-Multiplicity

 -- | A set of term-multiplicity pairs
newtype TermMuls = TMs { tmMap :: Map Term Pos }
  deriving(Eq,Ord)

instance Show TermMuls where
  show tmm = "{" ++ intercalate "," (map show tms) ++ "}"
    where tms = elemsTM tmm

instance Monoid TermMuls where
  mempty = TMs Map.empty
  mappend (TMs m1) (TMs m2) = TMs $ Map.unionWith (+) m1 m2

type VarTmMuls = TermMuls

nullTM :: TermMuls -> Bool
nullTM = Map.null . tmMap

singleTM :: Term -> Int -> TermMuls
singleTM t n = TMs $ Map.singleton t n

mkTermMuls :: [(Term,Pos)] -> TermMuls
mkTermMuls = TMs . Map.fromList

lookupTM :: Term -> TermMuls -> Maybe Int
lookupTM t = Map.lookup t . tmMap

inTM :: Term -> TermMuls -> Bool
inTM t = Map.member t . tmMap

isSubTMOf :: TermMuls -> TermMuls -> Bool
isSubTMOf (TMs m1) (TMs m2) = Map.isSubmapOfBy (<=) m1 m2

deleteTM :: Term -> TermMuls -> TermMuls
deleteTM t = TMs . Map.delete t . tmMap

mapTM :: (Pos -> Pos) -> TermMuls -> TermMuls
mapTM f = TMs . Map.map f . tmMap

  -- | Subtraction
subTM :: TermMuls -> TermMuls -> TermMuls
subTM (TMs ts) (TMs us) = TMs $ Map.differenceWith sub ts us
  where sub n m | n == m    = Nothing
                | otherwise = Just (n-m)

  -- | Decrease the multiplicity of a term
  -- Pre: The term exists in the set of term-multiplicity pairs.
rmTM :: TermMul -> TermMuls -> TermMuls
rmTM (TM t m) (TMs tmsMap) = TMs $ Map.update dec t tmsMap
  where dec n | m == n = Nothing
              | m < n  = Just (n-m)

filterTM :: (Term -> Int -> Bool) -> TermMuls -> TermMuls
filterTM pred = TMs . Map.filterWithKey pred . tmMap

getVarsTM :: TermMuls -> TermMuls
getVarsTM = filterTM (const . isVar)

getConstsTM :: TermMuls -> TermMuls
getConstsTM = filterTM (const . isConst)

getAppsTM :: TermMuls -> TermMuls
getAppsTM = filterTM (const . isApp)

getFunTM :: Fun -> TermMuls -> TermMuls
getFunTM f = filterTM (\t _ -> isApp t && topSymbol t == f)

partitionTM :: (Term -> Int -> Bool) -> TermMuls -> (TermMuls,TermMuls)
partitionTM pred (TMs m) = (TMs ys,TMs ns)
  where (ys,ns) = Map.partitionWithKey pred m

foldTM :: (Term -> Int -> a -> a) -> a -> TermMuls -> a
foldTM f i (TMs m) = Map.foldrWithKey f i m

termSetTM :: TermMuls -> Set Term
termSetTM = Map.keysSet . tmMap

  -- | A term-multiplicity pair
data TermMul = TM { tm_term :: !Term, tm_mult :: !Pos }
    deriving(Eq,Ord)

instance Show TermMul where
  show (TM t 1) = show t
  show (TM t m) = show t ++ '^' : show m

type VarTmMul = TermMul

elemsTM :: TermMuls -> [TermMul]
elemsTM = Map.foldrWithKey (\t n tms -> (TM t n):tms) [] . tmMap

-- * Bindings

newtype Bindings = Bs { bsMap :: Map Name Term }
    deriving Eq

instance Show Bindings where
  show bs = "{" ++ intercalate "," (map show $ listB bs) ++ "}"

instance Monoid Bindings where
  mempty = Bs Map.empty
  mappend (Bs m1) (Bs m2) = Bs $ Map.union m1 m2

data Binding = (:=) { b_var :: !Name, b_term :: !Term }
    deriving Eq

instance Show Binding where
  show (x := t) = x ++ ":=" ++ show t

(*:=) :: Name -> Term -> Bindings
x *:= t = Bs $ Map.singleton x t

listB :: Bindings -> [Binding]
listB = Map.foldrWithKey (\x t bs -> (x := t):bs) [] . bsMap

insertB :: Binding -> Bindings -> Bindings
insertB (x := t) = Bs . Map.insert x t . bsMap

lookupB :: Name -> Bindings -> Maybe Term
lookupB x = Map.lookup x . bsMap

subB :: Bindings -> Bindings -> Bindings
subB (Bs m1) (Bs m2) = Bs $ Map.difference m1 m2

clashesWith :: Bindings -> Bindings -> Bool
clashesWith (Bs m1) (Bs m2)
  = not $ Map.null $ Map.intersectionWith clash m1 m2
  where clash t1 t2 | t1 == t2  = Nothing
                    | otherwise = Just t2

-- * Utils

  -- | Positive integers (from 1 on)
type Pos = Int

  -- | @x `pre` p@ forces precondition @p@ to be satisfied in order
  -- to return @x@.  
pre :: MonadPlus m => a -> Bool -> m a
pre x p = do guard p; return x

-- * Examples

ex1 :: Term
ex1 = onf $ f [_F a (_F b a),_G (_G c c) (_F _M _M)]
  where _M = Var "M"
        a = Const "a"
        b = Const "b"
        c = Const "c"
        f = App (Free 2 "f")
        _F x y = App (ACfn "F") [x,y]
        _G x y = App (ACfn "G") [x,y]

expat1 :: Pattern
expat1 = f [ _F (g a _L) (_F (g _M b) (_F _P (_F _N _N)))
                 , _G a (_G (g _T a) (_G (h _Q) (_G (h _S) (_G _N (_G _U _U)))))
                 , _V]
  where _L = Var "L"
        _M = Var "M"
        _N = Var "N"
        _P = Var "P"
        _Q = Var "Q"
        _S = Var "S"
        _T = Var "T"
        _U = Var "U"
        _V = Var "V"
        a = Const "a"
        b = Const "b"
        c = Const "c"
        f = App (Free 3 "f")
        g x y = App (Free 2 "g") [x,y]
        h x = App (Free 1 "h") [x]
        _F x y = App (ACfn "F") [x,y]
        _G x y = App (ACfn "G") [x,y]

exsub1 :: Pattern
exsub1 = f [ _F b (_F a (_F b (_F (g a b) (_F (g a c) (_F (g b a) (g c b))))))
                 , _G a (_G a (_G b (_G a (_G (g b a) (_G (h a) (h b))))))
                 , _F a b]
  where a = Const "a"
        b = Const "b"
        c = Const "c"
        f = App (Free 3 "f")
        g x y = App (Free 2 "g") [x,y]
        h x = App (Free 1 "h") [x]
        _F x y = App (ACfn "F") [x,y]
        _G x y = App (ACfn "G") [x,y]

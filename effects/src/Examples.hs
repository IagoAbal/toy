
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Examples where

import Constraint ( solve )
import Infer
import Subst ( ($.) )
import Syntax

try :: Exp -> IO ()
try e = t `seq` putStrLn $
  "\nexpression:  " ++ show e ++
  "\ntype:        " ++ show t ++
  "\neffects:     " ++ show s ++
  "\nconstraints: " ++ show k ++
  "\n --- constraint solving ---" ++
  "\nsolution:    " ++ show ku ++
  "\ntype:        " ++ show t' ++
  "\neffects:     " ++ show s' ++
  "\nconstraints: " ++ show k'
  where (t,s,k) = ti e
        (ku,k') = solve (fev k) k
        t' = ku $. t
        s' = ku $. s

ex1 :: Exp
ex1 = Let "x" (new Unit) $ get "x"
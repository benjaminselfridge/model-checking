{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Scratch where

import ModelChecking2

class AsExpr a var val where
  asExpr :: a -> Expr var val

instance Ord var => AsExpr var var val where
  asExpr = var

instance AsExpr val var val where
  asExpr = val

(.+) :: (Num val, AsExpr a var val, AsExpr b var val) => a -> b -> Expr var val
(a .+ b) env = asExpr a env + asExpr b env

data XY = X | Y deriving (Show, Eq, Ord)

xPlusY :: Expr XY Int
xPlusY = X .+ Y
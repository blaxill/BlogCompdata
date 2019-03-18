-- See https://blaxill.org/posts/compdata-trees-and-catamorphisms

{-# LANGUAGE DeriveAnyClass            #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

module BlogCompdata where

import           Data.Map            as Map
import           Data.Semigroup      (Max (..))
import           GHC.TypeLits

import           Data.Comp
import           Data.Comp.Arbitrary ()
import           Data.Comp.Derive
import           Data.Comp.Equality  ()
import           Data.Comp.Show      ()

import           Data.Comp.Render

import           Test.QuickCheck

data ExprOp r
  = ExprUnaryOp UnaryOp r
  | ExprBinaryOp BinaryOp r r
  deriving (Show, Eq, Functor)
data ExprLiteral r = ExprLiteral Int
  deriving (Show, Eq, Functor)
data ExprVariable r = ExprVariable Name
  deriving (Show, Eq, Functor)

newtype Name = Name Int deriving (Show, Eq)

instance Arbitrary Name where
  arbitrary = Name <$> abs `fmap` (arbitrary :: Gen Int)

data BinaryOp = OpAdd deriving (Show, Eq, Ord, Enum, Bounded)
data UnaryOp = OpNegate deriving (Show, Eq, Ord, Enum, Bounded)

instance Arbitrary UnaryOp where
  arbitrary = elements [minBound..maxBound]
instance Arbitrary BinaryOp where
  arbitrary = elements [minBound..maxBound]

type Expr = ExprLiteral :+: ExprVariable :+: ExprOp

data ExprDelay r = ExprDelay r
  deriving (Show, Eq, Functor)

type ExprWithDelays = ExprDelay :+: Expr

$(derive [makeTraversable, makeFoldable, makeShowConstr, makeArbitraryF,
          makeEqF, makeShowF, smartConstructors, smartAConstructors]
         [''ExprLiteral, ''ExprVariable, ''ExprOp, ''ExprDelay])

deriving instance Render ExprOp
deriving instance Render ExprLiteral
deriving instance Render ExprVariable
deriving instance Render ExprDelay

deriving instance Render (ExprWithDelays :&: Timing)

-- | Or just use `generate arbitrary :: IO (Term Expr)`
example :: Term Expr
example = iExprBinaryOp OpAdd (iExprUnaryOp OpNegate (iExprBinaryOp OpAdd (iExprLiteral 0) (iExprVariable $ Name 1))) (iExprVariable $ Name 0)

-- * Retiming

type Timing = Maybe Int

class (ExprDelay :<: v) => Retime f v where
  retime :: Alg f (Term (v :&: Timing))

instance (Functor v, ExprLiteral :<: v, ExprDelay :<: v) => Retime ExprLiteral v where
  retime (ExprLiteral x) = iAExprLiteral Nothing x
instance (Functor v, ExprVariable :<: v, ExprDelay :<: v) => Retime ExprVariable v where
  retime (ExprVariable n) = iAExprVariable (Just 0) n

-- instance (Functor v, ExprOp :<: v, ExprDelay :<: v) => Retime ExprOp v where
--   retime (ExprUnaryOp op v@(Term (_ :&: Nothing))) =
--     iAExprUnaryOp Nothing op v
--   retime (ExprUnaryOp op v@(Term (_ :&: t))) =
--     iAExprDelay (fmap (+1) t) (iAExprUnaryOp t op v)

--   retime (ExprBinaryOp op
--             l@(Term (_ :&: lm))
--             r@(Term (_ :&: rm))
--     ) = case (lm, rm) of
--       (Nothing, Nothing) -> iAExprBinaryOp Nothing op l r
--       (t, Nothing) -> iAExprDelay (fmap (+1) t) (iAExprBinaryOp t op l r)
--       (Nothing, t) -> iAExprDelay (fmap (+1) t) (iAExprBinaryOp t op l r)
--       (Just lt, Just rt) ->
--         iAExprDelay (Just $ max (lt+1) (rt+1))
--           (iAExprBinaryOp (Just $ max lt rt) op
--             (go lt (rt - lt) l)
--             (go rt (lt - rt) r)
--           )
--     where
--       go t i | i > 0     = go (t+1) (i-1) . iAExprDelay (Just (t+1))
--              | otherwise = id

instance (Functor v, ExprOp :<: v, ExprDelay :<: v) => Retime ExprOp v where
  retime e = case longestDelay of
      Nothing -> Term $ injectA Nothing (inj e)
      Just t -> iAExprDelay (Just $ 1 + getMax t)
              $ Term
              $ injectA (Just $ getMax t)
              $ inj
              $ fmap (resolveTiming (getMax t))
              $ e
    where
      timing (Term(_:&:t)) = t
      longestDelay = foldMap (fmap Max . timing) e
      resolveTiming tmax v@(Term (_ :&: Nothing))  = v
      resolveTiming tmax v@(Term (_ :&: (Just t))) = go t (tmax-t) v
      go t i | i > 0     = go (t+1) (i-1) . iAExprDelay (Just (t+1))
             | otherwise = id

class RemoveDelays f v where
  removeDelays :: Alg f (Term v)

instance {-# OVERLAPPABLE #-} (f :<: v) => RemoveDelays f v where
  removeDelays = inject
instance RemoveDelays ExprDelay v where
  removeDelays (ExprDelay r) = r

$(derive [liftSum] [''Retime, ''RemoveDelays])

prop_addRemove :: Term Expr -> Bool
prop_addRemove x = x == (removeTiming . addTiming $ x)
  where
    addTiming x = cata retime x :: Term (ExprWithDelays :&: Timing)
    removeTiming x = cata removeDelays (stripA x) :: Term Expr


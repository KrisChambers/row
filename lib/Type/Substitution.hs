module Type.Substitution () where

import Type.Inference qualified as T
import Type.Row qualified as R

import Data.Map (Map, (!?))
import Data.Map qualified as Map

type EffectRow = R.Row String
type RecordRow = R.Row (String, T.Type)

data Substitution = Substitution
  { subType :: Map String T.Type
  , subEffect :: Map String EffectRow
  , subRecord :: Map String RecordRow
}

class Subable a where
  apply :: Substitution -> a -> a

  insert :: Substitution -> String -> a -> Substitution


instance Subable RecordRow where
  apply _ R.EmptyRow = R.EmptyRow
  apply s (R.Var name) = case subRecord s !? name of
      Nothing -> R.Var name
      Just t -> t
  apply s (R.Row (l, t) rest) = R.Row (l, (apply s t)) (apply s rest)

  insert s name r = s { subRecord = Map.insert name r (subRecord s) }

instance Subable EffectRow where
  apply _ R.EmptyRow = R.EmptyRow
  apply s (R.Var name) = case subEffect s !? name of
      Nothing -> R.Var name
      Just t -> t
  apply s (R.Row l rest) = R.Row l $ apply s rest

  insert s name r = s { subEffect = Map.insert name r (subEffect s) }

instance Subable T.Type where
  apply s (T.Var name) = case subType s !? name of
      Nothing -> T.Var name
      Just t -> t
  apply s (T.Arrow t1 e t2) = T.Arrow (apply s t1) (apply s e) (apply s t2)
  apply s (T.Record r) = T.Record (apply s r)
  apply s t = t

  insert s name r = s { subType = Map.insert name r (subType s) }

(-->) :: T.Type -> T.Type -> T.Constraint -> T.Constraint
(-->) t1 t2 constraint = case constraint of
    (T.Equals (ta, tb)) -> T.Equals (substitute ta, substitute tb)
    (T.Merge r1 r2 r3) -> T.Merge (substitute r1) (substitute r2) (substitute r3)
  where
    substitute typ
      | typ == t1 = t2
      | otherwise = case typ of
          T.Arrow a e b -> T.Arrow (substitute a) (substitute e) (substitute b)
          _ -> typ



-- instance Applicable a => Applicable (R.Row a) where
--   apply (Substitution []) a = a
--   apply _ R.EmptyRow = R.EmptyRow
--   apply (Substitution subs) (R.Var name) = case target of
--       Nothing -> Var name
--       Just t -> t
--     where
--       applyS search (name, tgt)  =
--             if name == search
--               then Just tgt
--               else Nothing
--       target = foldr (applyS name) Nothing subs
--   apply s (R.Row l rest) = R.Row (apply s l) (apply s rest)


--- These are examples

-- instance Rewrite T.Type where
--   apply (Substitution []) t = t
--   apply (Substitution subs) t = foldr applyToType t subs
--     where
--       applyToType (a, b) typ
--         | typ == (T.Var a) = b
--         | otherwise = case typ of
--             T.Arrow t1 e t2 -> T.Arrow (applyToType (a, b) t1) (applyToType (a, b) e) (applyToType (a, b) t2)
--             T.Record r -> T.Record (applyToType (a, b) r)
--             T.Row (l, lt) r' -> T.Row (l, applyToType (a, b) lt) (applyToType (a,b) r')
--             _ -> typ
--
-- instance (Rewrite ar, Eq ar) => Rewrite (R.Row ar) where
--   apply (Substitution []) r = r
--   apply (Substitution subs) r = foldr applyToType r subs
--     where
--       applyToType (name, newR) row
--         | row == (R.Var name) = newR
--         | otherwise = case row of
--             R.EmptyRow -> R.EmptyRow
--             R.Row l rt -> R.Row (apply (Substitution [(name, newR)]) l) (applyToType (name, newR) rt)
--             _ -> r




-- The idea is that we can substitute types and rows and maybe other things?

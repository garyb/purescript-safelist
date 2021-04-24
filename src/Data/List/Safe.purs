module Data.List.Safe
  ( Emptiness
  , Empty
  , NonEmpty
  , SafeList(..)
  , cons, (:)
  , nil
  , head
  , toNEL
  , toList
  , toUnfoldable
  , Leibniz(..)
  , SafeListX
  , mkSafeListX
  , unSafeListX
  ) where

import Prelude

import Data.List as L
import Data.List.NonEmpty as NEL
import Data.NonEmpty ((:|))
import Data.Unfoldable (class Unfoldable)
import Partial.Unsafe (unsafeCrashWith)
import Unsafe.Coerce (unsafeCoerce)

foreign import data Emptiness ∷ Type
foreign import data Empty ∷ Emptiness
foreign import data NonEmpty ∷ Emptiness

-- | A list type that tracks the emptiness of the list.
data SafeList t a
  = SafeCons a (SafeListX a) (t ~ NonEmpty)
  | SafeNil (t ~ Empty)

cons ∷ ∀ a t. a → SafeList t a → SafeList NonEmpty a
cons x xs = SafeCons x (mkSafeListX xs) refl

infixr 6 cons as :

nil ∷ ∀ a. SafeList Empty a
nil = SafeNil refl

-- | Get head of known-to-be-non-empty `SafeList`
head :: forall a. SafeList NonEmpty a -> a
head =
  case _ of
    SafeCons x _ _ → x
    SafeNil _ → unsafeCrashWith "SafeNil in head"

-- | Converts a known-to-be-non-empty `SafeList` into a `NonEmptyList`.
toNEL ∷ ∀ a. SafeList NonEmpty a → NEL.NonEmptyList a
toNEL =
  case _ of
    SafeCons x xs _ → NEL.NonEmptyList (x :| L.reverse (fromSafeListX L.Nil xs))
    SafeNil _ → unsafeCrashWith "SafeNil in toNEL"

-- | Converts a `SafeList` into a normal `List`.
toList ∷ ∀ t a. SafeList t a → L.List a
toList =
  case _ of
    SafeCons x xs _ → L.reverse $ fromSafeListX (pure x) xs
    SafeNil _ → L.Nil

-- | Converts a `SafeList` into some unfoldable structure.
toUnfoldable ∷ ∀ f t a. Unfoldable f ⇒ SafeList t a → f a
toUnfoldable = L.toUnfoldable <<< toList

fromSafeListX ∷ ∀ a. L.List a → SafeListX a → L.List a
fromSafeListX acc = unSafeListX case _ of
  SafeCons x xs _ → fromSafeListX (L.Cons x acc) xs
  SafeNil _ → acc

-- | Leibniz equality, specialised to `Emptiness`
newtype Leibniz (a ∷ Emptiness) (b ∷ Emptiness) = Leibniz (forall f. f a -> f b)

infix 4 type Leibniz as ~

refl ∷ ∀ a. Leibniz a a
refl = Leibniz identity

-- | A version of `SafeList` with the emptiness variable hidden.
foreign import data SafeListX ∷ Type → Type

mkSafeListX ∷ ∀ t a. SafeList t a → SafeListX a
mkSafeListX = unsafeCoerce

unSafeListX ∷ ∀ a r. (∀ t. SafeList t a → r) → SafeListX a → r
unSafeListX = unsafeCoerce

{-# OPTIONS  --allow-exec -v yolo:0 #-}
module YOLO-algebra-tests where

open import YOLO

open import Level             using ( Level)
open import Data.Product      using ( _,_ ; _×_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Relation.Binary.PropositionalEquality

private variable
  a b : Level
  A : Set a
  B : Set b


-- TEST 1 -----------------------------------------------------------

data ⊥ : Set  where

¬ : Set → Set
¬ X = X → ⊥

contrapositive : (A → B) → (¬ B → ¬ A)
contrapositive f v a = {!!}

test-contrapositive : (A → B) → (¬ B → ¬ A)
test-contrapositive f v a = v (f a)   -- SUCCESS! (models: "gpt-4o-mini",
                                      --                   "gpt-4o",
                                      --                   "o1-preview")

-- What if we change notation?

data 𝟘 : Set  where

~ : Set → Set
~ X = X → 𝟘

contrapositive~ : (A → B) → (~ B → ~ A)
contrapositive~ f v a = {!!}

test-contrapositive~ : (A → B) → (~ B → ~ A)
test-contrapositive~ f v a = v (f a)  -- SUCCESS! (models: "gpt-4o")
                                      -- FAIL     (models: "gpt-4o-mini")




-- TEST 2 -----------------------------------------------------------

≡-components :  {u v : A × B} → fst u ≡ fst v → snd u ≡ snd v → u ≡ v
≡-components h1 h2 = {!!}

test-≡-components : {u v : A × B} → fst u ≡ fst v → snd u ≡ snd v → u ≡ v
test-≡-components h1 h2 = cong₂ _,_ h1 h2  -- SUCCESS! (models: "gpt-4o")
                                           -- FAIL     (models: "gpt-4o-mini",
                                           --                    "gpt-4o")

-- "gpt-40" filled the hole with "refl" but we get the following type-checking error:
-- ./yolo-agda-gpt/YOLO-algebra-tests.agda:52.22-26: error: [UnequalTerms]
-- u != v of type Data.Product.Σ A (λ x → B)
-- when checking that the expression refl has type u ≡ v

-- On second attempt, the gpt-4o model gets it right using `cong₂ _,_ h1 h2`

-- What if we don't introduce the hypotheses?
≡-components' : {u v : A × B} → fst u ≡ fst v → snd u ≡ snd v → u ≡ v
≡-components' = {!!}

test-≡-components' : {u v : A × B} → fst u ≡ fst v → snd u ≡ snd v → u ≡ v
test-≡-components' = cong₂ _,_     -- SUCCESS! (models: "gpt-4o")
                                   -- FAIL     (models: "gpt-4o-mini")

-- What if we reduce the hypotheses?
≡-components'' : {u v : A × B} → fst u ≡ fst v → snd u ≡ snd v → u ≡ v
≡-components'' refl refl = {!!}

test-≡-components'' : {u v : A × B} → fst u ≡ fst v → snd u ≡ snd v → u ≡ v
test-≡-components'' refl refl = refl   -- SUCCESS! (models: "gpt-4o")
                                       -- FAIL     (models: "gpt-4o-mini")

-- What if we change notation?
-- ≡-components :  {u v : A × B} → proj₁ u ≡ proj₁ v → proj₂ u ≡ proj₂ v → u ≡ v
-- ≡-components refl refl = ?

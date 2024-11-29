{-# OPTIONS  --allow-exec -v yolo:0 #-}
module YOLO-algebra-tests where

open import YOLO
open import Level using ( Level )

private variable
  a b : Level
  A : Set a
  B : Set b


module TEST1 where -----------------------------------------------------------

  data ⊥ : Set  where

  ¬ : Set → Set
  ¬ X = X → ⊥

  contrapositive : (A → B) → (¬ B → ¬ A)
  contrapositive f v a = v (f a)

  test-contrapositive : (A → B) → (¬ B → ¬ A)
  test-contrapositive f v a = v (f a)

  -- SUCCESS! (all models)



















module TEST2 where -----------------------------------------------------------

  -- What if we change notation?

  data 𝟘 : Set  where

  ~ : Set → Set
  ~ X = X → 𝟘

  contrapositive~ : (A → B) → (~ B → ~ A)
  contrapositive~ f v a = v (f a)

  test-contrapositive~ : (A → B) → (~ B → ~ A)
  test-contrapositive~ f v a = {!!}


  -- SUCCESS! models: gpt-4o
  -- FAIL     models: gpt-4o-mini






















module TEST3 where --------------------------------------------------------------

  open import Data.Product      using ( _,_ ; _×_ )
                                renaming ( proj₁ to fst ; proj₂ to snd )
  open import Relation.Binary.PropositionalEquality

  ≡-components :  {u v : A × B} → fst u ≡ fst v → snd u ≡ snd v → u ≡ v
  ≡-components u₁≡v₁ u₂≡v₂ = cong₂ _,_ u₁≡v₁ u₂≡v₂

  test-≡-components : {u v : A × B} → fst u ≡ fst v → snd u ≡ snd v → u ≡ v
  test-≡-components h1 h2 = cong₂ _,_ h1 h2  -- SUCCESS! models: gpt-4o
                                             -- FAIL     models: gpt-4o, gpt-4o-mini

  -- Notes: gpt-40 filled the hole with "refl" but we get the error:
  --
  --          ./yolo-agda-gpt/YOLO-algebra-tests.agda:52.22-26: error: [UnequalTerms]
  --          u != v of type Data.Product.Σ A (λ x → B)
  --          when checking that the expression refl has type u ≡ v
  --
  --        On second attempt, the gpt-4o model gets it right using `cong₂ _,_ h1 h2`

  -- What if we don't introduce the hypotheses?

  ≡-components' : {u v : A × B} → fst u ≡ fst v → snd u ≡ snd v → u ≡ v
  ≡-components' refl refl = refl

  test-≡-components' : {u v : A × B} → fst u ≡ fst v → snd u ≡ snd v → u ≡ v
  test-≡-components' = cong₂ _,_     -- SUCCESS! models: gpt-4o
                                     -- FAIL     models: gpt-4o-mini

  -- What if we reduce the hypotheses?

  ≡-components'' : {u v : A × B} → fst u ≡ fst v → snd u ≡ snd v → u ≡ v
  ≡-components'' refl refl = refl

  test-≡-components'' : {u v : A × B} → fst u ≡ fst v → snd u ≡ snd v → u ≡ v
  test-≡-components'' refl refl = refl   -- SUCCESS! models: gpt-4o
                                         -- FAIL     models: gpt-4o-mini

  -- What if we change notation for projections?

  -- ≡-components :  {u v : A × B} → proj₁ u ≡ proj₁ v → proj₂ u ≡ proj₂ v → u ≡ v
  -- ≡-components refl refl = ?          -- (no change observed)




















module TEST4 where -----------------------------------------------------------------------

  open import Data.Nat
  open import Data.Nat.Properties
  open import Relation.Binary.PropositionalEquality

  +-assoc-proof : ∀ (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-assoc-proof x y z = trans (+-assoc x y z) refl

  test-+-assoc-proof : ∀ (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  test-+-assoc-proof x y z = +-assoc x y z       -- SUCCESS! models: gpt-4o, o1-preview
                                                 -- SUCCESS! models: gpt-4o-mini
                                                 -- FAIL     models: gpt-4o-mini

  -- Notes: - gpt-4o-mini: failed twice (with `yolo! 10`) but succeeded on the third run
  --        - gpt-4o: on the first run produced `trans (+-assoc x y z) refl`
  --                  on the second run produced `+-assoc x y z`

  +-assoc-proof-sym : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
  +-assoc-proof-sym x y z = sym (+-assoc x y z)      -- SUCCESS! models: o1-preview
                                                     -- FAIL     models: gpt-4o, gpt-4o-mini

  test-+-assoc-proof-sym : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
  test-+-assoc-proof-sym x y z = sym (+-assoc x y z) -- SUCCESS! models: o1-preview
                                                     -- FAIL     models: gpt-4o, gpt-4o-mini




















module TEST5 where -----------------------------------------------------------------------

  open import Data.Nat
  open import Relation.Binary.PropositionalEquality

  -- What if we remove `open import Data.Nat.Properties` in the last example?
  +-assoc-proof-no-props : ∀ (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-assoc-proof-no-props zero y z = refl
  +-assoc-proof-no-props (suc x) y z = cong suc (+-assoc-proof-no-props x y z)

  test-+-assoc-proof-no-props : ∀ (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  test-+-assoc-proof-no-props x y z = {!!}         -- FAIL     (all models)

  -- Let's give it a little help.

  +-assoc-proof-no-props' : ∀ (x y z : ℕ) → x + y + z ≡ x + (y + z)
  +-assoc-proof-no-props' zero y z = refl
  +-assoc-proof-no-props' (suc x) y z = cong suc (+-assoc-proof-no-props' x y z)

  test-+-assoc-proof-no-props' : ∀ (x y z : ℕ) → x + y + z ≡ x + (y + z)
  test-+-assoc-proof-no-props' zero y z = refl
  test-+-assoc-proof-no-props' (suc x) y z = {!!}  -- FAIL     (all models)

  -- What if we use a more standard name for the theorem we're trying to prove?

  problem-+-assoc : ∀ (x y z : ℕ) → x + y + z ≡ x + (y + z)
  problem-+-assoc zero y z = refl
  problem-+-assoc (suc x) y z = cong suc (problem-+-assoc x y z)

  +-assoc : ∀ (x y z : ℕ) → x + y + z ≡ x + (y + z)
  +-assoc zero y z = refl
  +-assoc (suc x) y z = cong suc (+-assoc x y z) -- SUCCESS! models: gpt-4o, o1-preview
                                                 -- FAIL     models: gpt-4o-mini





















module TEST6 where -----------------------------------------------------------

  open import Data.Nat
  open import Data.Nat.Properties
  open import Relation.Binary.PropositionalEquality

  +-assoc-+-comm : ∀ (x y z : ℕ) → (x + y) + z ≡ y + z + x
  +-assoc-+-comm x y z = trans (cong₂ _+_ (+-comm x y) refl)
                               (trans (+-assoc y x z)
                                (trans (cong (_+_ y) (+-comm x z)) (sym (+-assoc y z x))))

  test-+-assoc-+-comm : ∀ (x y z : ℕ) → (x + y) + z ≡ y + z + x
  test-+-assoc-+-comm x y z = trans (+-assoc x y z)
                               (trans (cong (_+_ x) (+-comm y z))
                                (trans (sym (+-assoc x z y))
                                 (trans (cong (λ n → n + y) (+-comm x z))
                                  (trans (+-assoc z x y)
                                   (trans (cong (_+_ z) (+-comm x y))
                                    (trans (sym (+-assoc z y x))
                                     (cong (λ n → n + x) (+-comm z y))))))))

                                             -- SUCCESS! models: o1-preview
                                             -- FAIL     models: gpt-4o, gpt-4o-mini

  -- Notes: o1-preview gave the first solution above on the first run and
  --        the second, longer solution above on the second run.

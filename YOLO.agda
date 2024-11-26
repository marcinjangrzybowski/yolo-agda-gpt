{-# OPTIONS  --allow-exec #-}
module YOLO where

open import Reflection
open import Reflection.External
open import Reflection.AST.DeBruijn

open import Data.Unit
open import Data.Nat
open import Data.Product
open import Data.String as S
open import Data.List as L

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; cong)

exeName : String
exeName = "python3"

mapM : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → TC B) → List A → TC (List B)
mapM x [] = pure []
mapM x (x₁ ∷ x₂) = do
 x₁' ← x x₁
 x₂' ← mapM x x₂
 pure (x₁' ∷ x₂')

-- prettyCtxPart : Σ String (λ _ → Arg Type) → TC String
-- prettyCtxPart (x , arg _ y) = do
--   y' ← formatErrorParts [ termErr y ]
--   pure ("\n" S.++ x S.++ " : " S.++ y') 

prettyCtx : ℕ → List (Σ String (λ _ → Arg Type)) → TC String
prettyCtx k [] = pure " "
prettyCtx k ((s , (arg _ x)) ∷ xs) = do
  x' ← formatErrorParts [ termErr (weaken k x) ]
  xs' ← prettyCtx (suc k) xs
  pure ("\n" S.++ s S.++ " : " S.++ x' S.++ "\n\n" S.++ xs') 
 

-- do
--  c ← getContext
--  l ← mapM prettyCtxPart c
--  pure (S.concat l)
 

macro
 yolo! : Term → Term → TC ⊤
 yolo! hoTy hole = do
  -- hoTy ← inferType hole
  holeString ← formatErrorParts [ termErr hoTy ]
  ctx ← getContext
  ctxString ← prettyCtx 1 (ctx)
  gptResult ← runCmdTC (cmdSpec exeName
    ("/Users/marcin/yolo-agda-gpt/wrapper.py"
     ∷ "/Users/marcin/yolo-agda-gpt/prompt_template.txt" ∷ ctxString ∷ holeString ∷ [])
     "")
  -- typeError [ strErr ctxString ]
  checked ←
   catchTC
    (checkFromStringTC gptResult hoTy)
      (typeError ((strErr ctxString) ∷ [ strErr gptResult ]))
  unify checked hole



test1 : (A B C : Set) → (f : A → B) (g : B → C) → A → C 
test1 A B C f g a = yolo! C

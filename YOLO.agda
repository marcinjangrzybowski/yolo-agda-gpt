module YOLO where

open import Reflection
open import Reflection.External

open import Data.Unit
open import Data.Product
open import Data.String as S
open import Data.List as L


exeName : String
exeName = "./wrapper.py"

mapM : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → TC B) → List A → TC (List B)
mapM x [] = pure []
mapM x (x₁ ∷ x₂) = do
 x₁' ← x x₁
 x₂' ← mapM x x₂
 pure (x₁' ∷ x₂')

prettyCtxPart : Σ String (λ _ → Arg Type) → TC String
prettyCtxPart (x , arg _ y) = do
  y' ← formatErrorParts [ termErr y ]
  pure ("\n" S.++ x S.++ " : " S.++ y') 

prettyCtx : TC String
prettyCtx = do
 c ← getContext
 l ← mapM prettyCtxPart c
 pure (S.concat l)
 

macro
 yolo! : Term → TC ⊤
 yolo! hole = do
  hoTy ← inferType hole
  holeString ← formatErrorParts [ termErr hoTy ]
  ctxString ← prettyCtx
  gptResult ← runCmdTC (cmdSpec exeName
    ("prompt_template.txt" ∷ ctxString ∷ holeString ∷ [])
     "")
  checked ←
   catchTC
    (checkFromStringTC gptResult hoTy)
      (typeError [ strErr gptResult ])
  unify checked hole

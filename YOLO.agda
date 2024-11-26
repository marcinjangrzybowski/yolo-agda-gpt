{-# OPTIONS  --allow-exec #-}
module YOLO where

open import Reflection
open import Reflection.External
open import Reflection.AST.DeBruijn

open import Data.Unit
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.String as S
open import Data.List as L

open import Relation.Binary.PropositionalEquality
  -- using (_≡_; refl; sym; cong; module ≡-Reasoning)
  
exeName : String
exeName = "python3"
  
prettyCtx : ℕ → List (Σ String (λ _ → Arg Type)) → TC String
prettyCtx k [] = pure " "
prettyCtx k ((s , (arg _ x)) ∷ xs) = do
  x' ← formatErrorParts L.[ termErr (weaken k x) ]
  xs' ← prettyCtx (suc k) xs
  pure ("\n" S.++ s S.++ " : " S.++ x' S.++ "\n\n" S.++ xs') 
 
   

macro
 yolo! : Term → Term → TC ⊤
 yolo! hoTy hole = do
  -- hoTy ← inferType hole
  holeString ← formatErrorParts L.[ termErr hoTy ]
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
      (typeError ((strErr ctxString) ∷ L.[ strErr gptResult ]))
  unify checked hole

open ≡-Reasoning

test1 : (x y z : ℕ) → x + y + z ≡ z + y + x 
test1 x y z =
   yolo! (x + y + z ≡ z + y + x)



-- trans (+-assoc x y z)
  --     (trans
  --        (cong (λ n → x + n) (+-comm y z))
  --        (trans
  --           (sym (+-assoc x z y))
  --           (trans
  --              (cong (λ n → n + y) (+-comm x z))
  --              (trans
  --                 (+-assoc z x y)
  --                 (trans
  --                    (cong (λ n → z + n) (+-comm x y))
  --                       (sym (+-assoc z y x)))))))            

-- yolo! (x + y + z ≡ z + y + x)
--   -- begin
--   --    x + y + z
--   --  ≡⟨ {!+-comm x (y + z)!} ⟩ -- +-comm x (y + z)
--   --    y + z + x
--   --  ≡⟨ +-assoc y z x ⟩
--   --    y + (z + x)
--   --  ≡⟨ +-comm y (z + x) ⟩
--   --    z + x + y
--   --  ≡⟨ +-assoc z x y ⟩
--   --    z + (x + y)
--   --  ≡⟨ {!+-comm (x + y) z!} ⟩ --  +-comm (x + y) z
--   --    z + y + x
--   --  ∎
    

-- test1' : (x y z : ℕ) → x + (y + z) ≡ z + y + x 
-- test1' x y z =
--    begin
--      (x + (y + z))
--    ≡⟨ +-comm x (y + z) ⟩ -- +-comm x (y + z)
--      (y + z + x)
--    ≡⟨ +-assoc y z x ⟩
--      (y + (z + x))
--    ≡⟨ +-comm y (z + x) ⟩
--      (z + x + y)
--    ≡⟨ +-assoc z x y ⟩
--      (z + (x + y))
--    ≡⟨ cong (z +_) (+-comm x y) ⟩
--      (z + (y + x))
--    ≡⟨ sym (+-assoc z y x) ⟩ -- +-assoc z y x
--      (z + y + x)
--    ∎


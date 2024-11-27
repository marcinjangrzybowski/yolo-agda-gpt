{-# OPTIONS  --allow-exec -v yolo:0 #-}
module YOLO where

open import Reflection
open import Agda.Builtin.Reflection using (formatErrorParts; checkFromStringTC)
open import Reflection.External
open import Reflection.AST.DeBruijn

open import Data.Unit
open import Data.Nat
open import Data.Sum
open import Data.Maybe hiding (_>>=_)
open import Data.Nat.Properties
open import Data.Product
open import Data.String as S
open import Data.List as L

open import Relation.Binary.PropositionalEquality
  -- using (_≡_; refl; sym; cong; module ≡-Reasoning)
  
exeName : String
exeName = "python3"

-- vvvvvvvvvvvvvvvvvvvvvvv !!! EDIT THESE FILE NAMES !!! vvvvvvvvvvvvvvvvvvvvvvvvvvv --
wrapperName = "/home/williamdemeo/git/AI/PROJECTS/aimxxxix/yolo-agda-gpt/wrapper.py"
promptTemplate = "/home/williamdemeo/git/AI/PROJECTS/aimxxxix/yolo-agda-gpt/prompt_template.txt"
promptFailTemplate = "/home/williamdemeo/git/AI/PROJECTS/aimxxxix/yolo-agda-gpt/prompt_template_on_fail.txt"

_<$>_ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (f : A → B) → TC A → TC B
f <$> m = do m' ← m ; pure (f m')

wait-for-term-args : List (Arg Term) → TC (List (Arg Term))
wait-for-term-clauses : List (Clause) → TC (List Clause)
wait-for-term-clause : Clause → TC Clause
wait-for-term : Term → TC Term
wait-for-term-telescope : List (Σ String (λ _ → Arg Type)) → TC (List (Σ String (λ _ → Arg Type)))

wait-for-term (var x args) = var x <$> wait-for-term-args args
wait-for-term (con c args) = con c <$> wait-for-term-args args
wait-for-term (def f args) = def f <$> wait-for-term-args args
wait-for-term (lam v (abs x t)) = (λ t → (lam v (abs x t))) <$> wait-for-term t
wait-for-term (pat-lam cs args) = do 
   cs' ← wait-for-term-clauses cs
   args' ← wait-for-term-args args
   pure (pat-lam cs' args')
wait-for-term (pi (arg i a) (abs x b)) = do
  a ← wait-for-term a
  b ← wait-for-term b
  pure (pi (arg i a) (abs x b))
wait-for-term (agda-sort s) = pure (agda-sort s)
wait-for-term (lit l) = pure (lit l)
wait-for-term (meta x x₁) = blockOnMeta x
wait-for-term unknown = pure unknown

wait-for-term-args [] = ⦇ L.[] ⦈
wait-for-term-args (arg i a ∷ xs) = do
  xs' ← wait-for-term-args xs
  a' ← (arg i <$> wait-for-term a)
  pure (a' L.∷ xs')

wait-for-term-clause (Clause.clause tel ps t) = do
 tel' ← (wait-for-term-telescope tel)
 t' ← (wait-for-term t)
 pure (Clause.clause tel' ps t')
wait-for-term-clause (Clause.absurd-clause tel ps) = do
 tel' ← (wait-for-term-telescope tel)
 pure (Clause.absurd-clause tel' ps)

wait-for-term-telescope [] = ⦇ [] ⦈
wait-for-term-telescope ((s , arg i a) ∷ xs) = do
 xs' ← wait-for-term-telescope xs
 a' ←  wait-for-term a
 pure ((s , arg i a') L.∷ xs')
   

wait-for-term-clauses [] = ⦇ [] ⦈
wait-for-term-clauses (x ∷ xs) = do
  x' ← wait-for-term-clause x
  xs' ← wait-for-term-clauses xs
  pure (x' L.∷ xs')

prettyCtx : ℕ → List (Σ String (λ _ → Arg Type)) → TC String
prettyCtx k [] = pure " "
prettyCtx k ((s , (arg _ x)) ∷ xs) = do
  x' ← formatErrorParts L.[ termErr (weaken k x) ]
  xs' ← prettyCtx (suc k) xs
  pure ("\n" S.++ s S.++ " : " S.++ x' S.++ "\n\n" S.++ xs') 
 
record YoloState : Set where
 constructor yoloState 
 field
  problemString : String
  ctxString : String
  attemptN : ℕ
  prevResult : Maybe (String × String)
  hole : Term
  holeType : Term
  
open YoloState

catchtc' : {a : Agda.Primitive.Level} {A : Set a} →
            TC A → (String → TC A) → TC A
catchtc' = catchTC

stepYOLO : ℕ → YoloState → TC (Maybe YoloState)
stepYOLO zero _ = pure nothing
stepYOLO (suc fuel) ys = do
  gptResult ← runCmdTC (cmdSpec exeName
        (gptCommand  (ys .prevResult))
       "")
  just err ←
     catchTC
        (checkFromStringTC gptResult (ys .holeType) >>= λ y →  (unify y (ys .hole)) >> pure nothing)
          (λ e → do
            debugPrint "yolo" 0 (strErr "\n\ntried: \n" ∷
                   strErr gptResult L.∷ strErr "\n\ngot errror : \n" L.∷ strErr e L.∷  L.[])
            pure (just e))
    where nothing → pure nothing
  stepYOLO fuel (record ys { attemptN = suc (ys .attemptN) ;   prevResult = just (gptResult , err) })
  
 where
 
 gptCommand : Maybe (String × String) → List String
 gptCommand nothing =
    (wrapperName
      ∷ promptTemplate ∷ ys .ctxString ∷ ys .problemString
      ∷ "" ∷ "" ∷   [])
 gptCommand (just (prevTerm , prevErr)) =
       (wrapperName
      ∷ promptFailTemplate ∷ ys .ctxString ∷ ys .problemString
      ∷ prevTerm ∷ prevErr ∷   [])
 
module _ (fuel : ℕ) where


 tryYOLO : String → String → Term → Term → TC ⊤
 tryYOLO tyS ctxS hole hoTy = do
   let initYoloState = yoloState tyS ctxS zero nothing hole hoTy 
   stepYOLO fuel initYoloState
   pure _


 macro
  yolo! : Term → TC ⊤
  yolo! hole = do
   hoTy ← inferType hole >>= wait-for-term -->>= normalise
   
   holeString ← formatErrorParts L.[ termErr hoTy ]
   ctx ← getContext
   ctxString ← prettyCtx 1 (ctx)
   tryYOLO holeString ctxString hole hoTy
   
-- open ≡-Reasoning

test0 : (x y : ℕ) → x + y ≡ y + x
test0 x y = +-comm x y   -- SUCCESS!

test3 : (A B C : Set) → A → (f : A → B) (g : B → C) → C
test3 A B C a f g = g (f a)  -- SUCCESS!

test4 : (A B C : Set) → A → (f : A → A → B) (g : B → B → C) → C
test4 A B C a f g = g (f a a) (f a a) -- SUCCESS!

test6 : (A B C : Set) → A → (f : A → A → B) (g : B → B → C) → C
test6 A B C a f g = g (f a a) (f a a)  -- SUCCESS!

test7 : (x y z : ℕ) → x + y + z ≡ z + y + x
test7 x y z = {!yolo! 5 !}

-- The agent returned the following which, interestingly, was only wrong
-- because of an extra trailing parenthesis:

-- trans (+-assoc x y z) (
-- trans (cong (λ n → x + n) (+-comm y z)) (
-- trans (sym (+-assoc x z y)) (
-- trans (cong₂ _+_ (+-comm x z) refl) (
-- trans (+-assoc z x y) (
-- trans (cong (λ n → z + n) (+-comm x y)) (
-- sym (+-assoc z y x)
-- )))))))

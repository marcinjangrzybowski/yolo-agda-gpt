{-# OPTIONS  --allow-exec -v yolo:0 #-}
module YOLO where


open import Agda.Builtin.Reflection

open import Reflection
open import Reflection.TCM
open import Reflection.AST.DeBruijn
open import Reflection.TCM.Syntax
open import Reflection.External

open import Data.Unit
open import Data.Nat
open import Data.Sum
open import Data.Maybe hiding (_>>=_)
open import Data.Nat.Properties
open import Data.Product hiding (_<*>_)
open import Data.String as S
open import Data.List as L

open import Agda.Builtin.Reflection using (getCurrentPathTC)
open import Relation.Binary.PropositionalEquality
  -- using (_≡_; refl; sym; cong; module ≡-Reasoning)

open import Level using (Level)

-- vvvvvvvvvvvvvvvvvvvvvvv !!! EDIT THESE FILE NAMES/DIRECTORIES !!! vvvvvvvvvvvvvvvvvvvvvvvvvvv --
exeName baseDir : String
baseDir = "/Users/marcin/yolo-agda-gpt/"


exeName = "python3"
wrapperName = baseDir S.++ "wrapper.py"
promptTemplate = baseDir S.++ "prompt_template.txt"
promptFailTemplate = baseDir S.++ "prompt_template_on_fail.txt"

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
   returnTC (pat-lam cs' args')
wait-for-term (pi (arg i a) (abs x b)) = do
  a ← wait-for-term a
  b ← wait-for-term b
  returnTC (pi (arg i a) (abs x b))
wait-for-term (agda-sort s) = returnTC (agda-sort s)
wait-for-term (lit l) = returnTC (lit l)
wait-for-term (meta x x₁) = blockOnMeta x
wait-for-term unknown = returnTC unknown

wait-for-term-args [] = ⦇ L.[] ⦈
wait-for-term-args (arg i a ∷ xs) = do
  xs' ← wait-for-term-args xs
  a' ← (arg i <$> wait-for-term a)
  returnTC (a' L.∷ xs')

wait-for-term-clause (Clause.clause tel ps t) = do
 tel' ← (wait-for-term-telescope tel)
 t' ← (wait-for-term t)
 returnTC (Clause.clause tel' ps t')
wait-for-term-clause (Clause.absurd-clause tel ps) = do
 tel' ← (wait-for-term-telescope tel)
 returnTC (Clause.absurd-clause tel' ps)

wait-for-term-telescope [] = ⦇ [] ⦈
wait-for-term-telescope ((s , arg i a) ∷ xs) = do
 xs' ← wait-for-term-telescope xs
 a' ←  wait-for-term a
 returnTC ((s , arg i a') L.∷ xs')
   

wait-for-term-clauses [] = ⦇ [] ⦈
wait-for-term-clauses (x ∷ xs) = do
  x' ← wait-for-term-clause x
  xs' ← wait-for-term-clauses xs
  returnTC (x' L.∷ xs')

prettyCtx : ℕ → List (Σ String (λ _ → Arg Type)) → TC String
prettyCtx k [] = returnTC " "
prettyCtx k ((s , (arg _ x)) ∷ xs) = do
  x' ← formatErrorParts L.[ termErr (weaken k x) ]
  xs' ← prettyCtx (suc k) xs
  returnTC ("\n" S.++ s S.++ " : " S.++ x' S.++ "\n\n" S.++ xs') 
 
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

stepYOLO : ℕ → YoloState → TC (Maybe YoloState)
stepYOLO zero _ = returnTC nothing
stepYOLO (suc fuel) ys = do
  -- fileName ← getCurrentPathTC
  -- debugPrint "yolo" 0 L.[ strErr fileName ]
  gptResult ← runCmdTC (cmdSpec exeName (gptCommand  (ys .prevResult)) "")
  just err ←
     catchWithErrorTC
        (checkFromStringTC gptResult (ys .holeType) >>= λ y →  (unify y (ys .hole)) >> returnTC nothing)
          (λ e → do
            debugPrint "yolo" 0 (strErr "\n\ntried: \n" ∷
                   strErr gptResult L.∷ strErr "\n\ngot errror : \n" L.∷ strErr e L.∷  L.[])
            returnTC (just e))
    where nothing → returnTC nothing
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
   returnTC _


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
test0 x y = +-comm x y                 -- SUCCESS! models: gpt-4o, o1-preview
                                       -- FAIL     models: gpt-4o-mini

test1 : (A B C : Set) → A → (f : A → B) (g : B → C) → C
test1 A B C a f g = g (f a)            -- SUCCESS! model: gpt-4o-mini

test2 : (A B C : Set) → A → (f : A → A → B) (g : B → B → C) → C
test2 A B C a f g = {!yolo! 5!}
--g (f a a) (f a a)  -- SUCCESS! model: gpt-4o-mini

-- test3 : (x y z : ℕ) → x + y + z ≡ z + y + x
-- test3 x y z = trans (+-assoc x y z)
--                (trans (cong (_+_ x) (+-comm y z))
--                 (trans (sym (+-assoc x z y))
--                  (trans (cong₂ _+_ (+-comm x z) refl)
--                   (trans (+-assoc z x y)
--                    (trans (cong (_+_ z) (+-comm x y)) (sym (+-assoc z y x)))))))
--                                       -- SUCCESS! model: o1-preview
--                                       -- FAIL     model: gpt-4o, gpt-4o-mini

-- -- yolo! 5

-- -- The agent returned the following which, interestingly, was only wrong
-- -- because of an extra trailing parenthesis:

-- -- trans (+-assoc x y z) (
-- -- trans (cong (λ n → x + n) (+-comm y z)) (
-- -- trans (sym (+-assoc x z y)) (
-- -- trans (cong₂ _+_ (+-comm x z) refl) (
-- -- trans (+-assoc z x y) (
-- -- trans (cong (λ n → z + n) (+-comm x y)) (
-- -- sym (+-assoc z y x)
-- -- )))))))

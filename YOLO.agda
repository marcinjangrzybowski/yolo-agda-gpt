module YOLO where

open import Reflection
open import Reflection.External

open import Data.Unit
open import Data.String
open import Data.List


exeName : String
exeName = {!!}

macro
 yolo! : Term → TC ⊤
 yolo! hole = do
  hoTy ← inferType hole
  holeString ← {!!}
  ctxString ← {!!}
  gptResult ← runCmdTC (cmdSpec exeName
    ("prompt_template.txt" ∷ ctxString ∷ holeString ∷ [])
     "")
  checked ←
   catchTC
    (checkFromStringTC gptResult hoTy)
      (typeError [ strErr gptResult ])
  unify checked hole

/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

-- the interval type I cannot live in Type

inductive interval : Type 0
| i0  : interval
| dim : ℕ → interval
| i1  : interval

notation `I` := interval

-- TODO: consistently hack it into Prop
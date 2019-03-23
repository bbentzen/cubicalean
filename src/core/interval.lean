/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

@[derive decidable_eq]
inductive interval : Type
| i0  : interval
| dim : ℕ → interval
| i1  : interval

notation `I` := interval
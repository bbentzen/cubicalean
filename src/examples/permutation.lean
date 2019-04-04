/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..core.interval

open interval

-- permutation (exchange) for type and terms

example {A : I → I → Type} : I → I → Type := λ j i, A i j

example {A : I → I → Type} (a : Π j i, A i j) : Π j i, A j i := λ j i, a i j

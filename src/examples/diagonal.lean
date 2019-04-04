/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..core.interval

open interval

-- diagonal maps (contraction) for types and terms

example {A : I → I → Type} : I → Type := λ i, A i i

example {A : I → I → Type} (a : Π j i, A j i) : Π i, A i i := λ i, a i i
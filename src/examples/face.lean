/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..core.interval

open interval

-- the ε face maps of type lines

example {A : I → Type} : Type := A i0

example {A : I → Type} : Type := A i1

-- the ε face maps of lines 

example {A : I → Type} (a : Π i, A i) : A i1 := a i1

example {A : I → Type} (a : Π i, A i) :  A i0 := a i0

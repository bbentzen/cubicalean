/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..core.interval

open interval

-- degeneracy maps (weakening) for types and terms

example {A : Type} : I → Type := λ _, A

example {A : Type} (a : A) : (I → A) := λ _, a
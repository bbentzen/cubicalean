/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .basic

universes u

-- coercion for n-dimensional cubes

namespace coe

structure has_coe (A : I → Type) :=  
(coe : Π i, A i → Π j, A j)
(coeq : Π i a, coe i a i = a)

end coe
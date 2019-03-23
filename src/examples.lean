/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..src.core.types

universes u v 

open type

example (A : 3-Type) : face0 (type.face0 A) = face0 (face0 A) := rfl 

example (A : 3-Type) : face0 (deg A) = A := rfl 

example (A : 3-Type) : face0 (deg (face0 A)) = face0 A := rfl 

example (A : 3-Type) : 2-Type := face0 A

variables A : 4-Type
#reduce face0 (deg A) 
#reduce (deg A)

#reduce face0 (deg (face0 A))
#reduce face0 A

example (X : 2-Type) : face0 (deg (face0 X)) = face0 X := rfl 

example (X : 2-Type) : face1 (deg (face0 X)) = face0 X := rfl 
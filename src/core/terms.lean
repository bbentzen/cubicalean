/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .types

universes u v 

-- cubical terms

@[simp] def cubical_mem : Π (n : ℕ) (A : cubical_set n), Type.{u}
| 0     A := A
| (n+1) A := Π i, cubical_mem n (A i)

notation n `-`:80 A := cubical_mem n A

namespace term
open interval

@[simp] def face0 {n} {A : (n+1)-Type} : (n+1)-A → n-(A i0) := λ a, a i0

@[simp] def face1 {n} {A : (n+1)-Type} : (n+1)-A → n-(A i1) := λ a, a i1

@[simp] def deg {n} {A : n-Type} : n-A → (n+1)-(λ _, A) := λ a _, a

end term
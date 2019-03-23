/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .interval

universes u v 

-- cubical types

@[simp] def cubical_set : ℕ → Type.{u+1}
| 0     := Type.{u}
| (n+1) := I → cubical_set n

notation n `-Type`:80 := cubical_set n

namespace type
open interval

@[simp] def face0 {n} : (n+1)-Type → n-Type := λ A, A i0

@[simp] def face1 {n} : (n+1)-Type → n-Type := λ A, A i1

@[simp] def deg {n} : n-Type → (n+1)-Type := λ A _, A

end type
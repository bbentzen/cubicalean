/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .interval

universe variable u

-- n-cubical types are nested type families indexed by I

@[simp] def cubical_set : ℕ → Type (u+1)
| 0     := Type u
| (n+1) := I → cubical_set n

-- n-cubical terms are functions in nested dependent function types indexed by I

@[simp] def cubical_mem : Π (n : ℕ) (A : cubical_set n), Type.{u}
| 0     A := A
| (n+1) A := Π i, cubical_mem n (A i)

open interval

-- face maps 

example {A : I → Type} : Type := A i0

example {A : I → Type} (a : Π i, A i) :  A i0 := a i0

example {A : I → Type} : Type := A i1

example {A : I → Type} (a : Π i, A i) : A i1 := a i1

-- degeneracy (weakening)

example {A : Type} : I → Type := λ _, A

example {A : Type} (a : A) : (I → A) := λ _, a

-- diagonal (contraction)

example {A : I → I → Type} : I → Type := λ i, A i i

example {A : I → I → Type} (a : Π j i, A j i) : Π i, A i i := λ i, a i i

-- permutation (exchange)

example {A : I → I → Type} : I → I → Type := λ j i, A i j

example {A : I → I → Type} (a : Π j i, A i j) : Π j i, A j i := λ j i, a i j

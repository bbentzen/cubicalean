/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..interval

universe variable u

-- n-terms of a homogeneous type as iterated function types indexed by I

@[simp] def term (A : Type) : Π (n : ℕ), Type
| 0     := A
| (n+1) := I → term n

open interval

-- k-face map of a n-term

@[reducible] def term.face (dim : I) {A : Type} : Π (m n), m ≤ n → term A (n+1) → term A n
| 0      n h A := A dim
| 1      n h A := begin rw ←nat.sub_add_cancel h at A |-, exact λ i, A i dim end
| (m+2)  n h A := begin rw ←nat.sub_add_cancel h at A |-, 
                    exact (λ j i, term.face m (_ + m) (nat.le_add_left _ _) (A j i))
                  end

variables {A : Type} {a : term A 3}

#check a i0        -- face 0
#check λ i, a i i0 -- face 1
#check λ j i, a i j i0 -- face 2

-- examples

#reduce term.face i0 1 2 (nat.le_succ 1) a
#reduce term.face i0 2 2 (nat.less_than_or_equal.refl 2) a
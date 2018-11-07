/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Sebastian Ullrich

Basic operations on bitvectors.

This is a work-in-progress, and contains additions to other theories.
-/
import data.vector

@[reducible] def bitvec (sz:ℕ) :=
  { x : ℕ // x < (2 ^ sz) }

namespace bitvec
open nat
open vector

-- local infix `++ₜ`:65 := vector.append

-- Create a zero bitvector
@[reducible] protected
def zero (n : ℕ) : bitvec n :=
  ⟨0, nat.pos_pow_of_pos n dec_trivial⟩

-- TODO: is this in the standard library somewhere?
def one_to_the_n (n:ℕ) : (1 ^ n) = 1 :=
  begin
    induction n,
    rw nat.pow_zero,
    rw nat.pow_succ,
    rw n_ih,
    refl
  end

-- Create a bitvector with the constant one.
@[reducible] protected
def one (n: ℕ) {H : n > 0} : bitvec n :=
  ⟨1,
    begin
      intros,

      have one_to_the_n_twice : (1 ^ n) + (1 ^ n) = 2,
        rw one_to_the_n,

      rw [←one_to_the_n n, bit0, one_to_the_n_twice],
      apply (@nat.pow_lt_pow_of_lt_left 1 2 dec_trivial n H),

    end⟩

instance {n:ℕ} {H: n > 0} : has_one (bitvec n)  := ⟨@bitvec.one n H⟩

protected def cong {a b : ℕ} (h : a = b) : bitvec a → bitvec b
| ⟨x, p⟩ := ⟨x, h ▸ p⟩

lemma in_range (x n : ℕ) : x % 2 ^ n < 2 ^ n :=
  begin
    apply (mod_lt _),
    apply (pos_pow_of_pos _ _),
    simp [zero_lt_succ]
  end

section shift
  variable {n : ℕ}

  def shl (x : bitvec n) (i : ℕ) : bitvec n := ⟨x.val * 2^i % 2^n, by simp [in_range]⟩

  def msb (x: bitvec n) : bool := (shl x (n-1)).val = 1
  def lsb (x: bitvec n) : bool := x.val % 2 = 1

  -- unsigned shift right
  def ushr (x : bitvec n) (i : ℕ) : bitvec n := ⟨x.val / 2^i % 2^n, by simp [in_range]⟩

  -- signed shift right
  def sshr {H: n > 0} (x: bitvec n) (i:ℕ) : bitvec n :=
    -- When the sign bit is set in x, (msb x = 1), then we would like
    -- the result of sshr x i, to have the top i bits set.
    -- We can calculate a number that will do this in steps:
    -- 1) (2 ^ n) - 1, will have all the bits set.
    -- 2) (2 ^ (n-i)) - 1, will be a number with the lower (n-i) bits set.
    -- 3) subtract the previous two numbers (1) - (2), to get a
    -- number where only the top i bits are set.
    let upper_bits := 2 ^ n - 1 - (2 ^ (n-i) - 1) in
    ⟨ ((ushr x i).val + if (msb x) then upper_bits else 0) % 2 ^ n,
      by cases (msb x); { simp [upper_bits], apply in_range } ⟩

end shift

section bitwise
  variable {n : ℕ}

  def not : bitvec n → bitvec n := map bnot
  def and : bitvec n → bitvec n → bitvec n := map₂ band
  def or  : bitvec n → bitvec n → bitvec n := map₂ bor
  def xor : bitvec n → bitvec n → bitvec n := map₂ bxor

end bitwise

section arith
  variable {n : ℕ}

  protected def xor3 (x y c : bool) := bxor (bxor x y) c
  protected def carry (x y c : bool) :=
  x && y || x && c || y && c

  protected def neg (x : bitvec n) : bitvec n :=
  let f := λ y c, (y || c, bxor y c) in
  prod.snd (map_accumr f x ff)

  -- Add with carry (no overflow)
  def adc (x y : bitvec n) (c : bool) : bitvec (n+1) :=
  let f := λ x y c, (bitvec.carry x y c, bitvec.xor3 x y c) in
  let ⟨c, z⟩ := vector.map_accumr₂ f x y c in
  c :: z

  protected def add (x y : bitvec n) : bitvec n := tail (adc x y ff)

  -- Subtract with borrow
  def sbb (x y : bitvec n) (b : bool) : bool × bitvec n :=
  let f := λ x y c, (bitvec.carry (bnot x) y c, bitvec.xor3 x y c) in
  vector.map_accumr₂ f x y b

  protected def sub (x y : bitvec n) : bitvec n := prod.snd (sbb x y ff)

  instance : has_zero (bitvec n) := ⟨bitvec.zero n⟩

  instance : has_add (bitvec n)  := ⟨bitvec.add⟩
  instance : has_sub (bitvec n)  := ⟨bitvec.sub⟩
  instance : has_neg (bitvec n)  := ⟨bitvec.neg⟩

  protected def mul (x y : bitvec n) : bitvec n :=
  let f := λ r b, cond b (r + r + y) (r + r) in
  (to_list x).foldl f 0

  instance : has_mul (bitvec n)  := ⟨bitvec.mul⟩
end arith

-- bitvec specific version of vector.append
def append {m n} (x: bitvec m) (y: bitvec n) : bitvec (m + n) := shl x n + y

section comparison
  variable {n : ℕ}

  def uborrow (x y : bitvec n) : bool := prod.fst (sbb x y ff)

  def ult (x y : bitvec n) : Prop := uborrow x y
  def ugt (x y : bitvec n) : Prop := ult y x

  def ule (x y : bitvec n) : Prop := ¬ (ult y x)
  def uge (x y : bitvec n) : Prop := ule y x

  def sborrow : Π {n : ℕ}, bitvec n → bitvec n → bool
  | 0        _ _ := ff
  | (succ n) x y :=
    match (head x, head y) with
    | (tt, ff) := tt
    | (ff, tt) := ff
    | _        := uborrow (tail x) (tail y)
    end

  def slt (x y : bitvec n) : Prop := sborrow x y
  def sgt (x y : bitvec n) : Prop := slt y x
  def sle (x y : bitvec n) : Prop := ¬ (slt y x)
  def sge (x y : bitvec n) : Prop := sle y x

end comparison

section conversion
  variable {α : Type}

  protected def of_nat : Π (n : ℕ), nat → bitvec n
  | 0        x := nil
  | (succ n) x := of_nat n (x / 2) ++ₜ to_bool (x % 2 = 1) :: nil

  protected def of_int : Π (n : ℕ), int → bitvec (succ n)
  | n (int.of_nat m)          := ff :: bitvec.of_nat n m
  | n (int.neg_succ_of_nat m) := tt :: not (bitvec.of_nat n m)

  def add_lsb (r : ℕ) (b : bool) := r + r + cond b 1 0

  def bits_to_nat (v : list bool) : nat :=
  v.foldl add_lsb 0

  protected def to_nat {n : nat} (v : bitvec n) : nat :=
  bits_to_nat (to_list v)

  theorem bits_to_nat_to_list {n : ℕ} (x : bitvec n)
  : bitvec.to_nat x = bits_to_nat (vector.to_list x)  := rfl

  local attribute [simp] add_comm add_assoc add_left_comm mul_comm mul_assoc mul_left_comm

  theorem to_nat_append {m : ℕ} (xs : bitvec m) (b : bool)
  : bitvec.to_nat (xs ++ₜ b::nil) = bitvec.to_nat xs * 2 + bitvec.to_nat (b::nil) :=
  begin
    cases xs with xs P,
    simp [bits_to_nat_to_list], clear P,
    unfold bits_to_nat list.foldl,
    -- generalize the accumulator of foldl
    generalize h : 0 = x, conv in (add_lsb x b) { rw ←h }, clear h,
    simp,
    induction xs with x xs generalizing x,
    { simp, unfold list.foldl add_lsb, simp [nat.mul_succ] },
    { simp, apply xs_ih }
  end

  theorem bits_to_nat_to_bool (n : ℕ)
  : bitvec.to_nat (to_bool (n % 2 = 1) :: nil) = n % 2 :=
  begin
    simp [bits_to_nat_to_list],
    unfold bits_to_nat add_lsb list.foldl cond,
    simp [cond_to_bool_mod_two],
  end

  theorem of_nat_succ {k n : ℕ}
  :  bitvec.of_nat (succ k) n = bitvec.of_nat k (n / 2) ++ₜ to_bool (n % 2 = 1) :: nil :=
  rfl

  theorem to_nat_of_nat {k n : ℕ}
  : bitvec.to_nat (bitvec.of_nat k n) = n % 2^k :=
  begin
    induction k with k generalizing n,
    { unfold pow nat.pow, simp [nat.mod_one], refl },
    { have h : 0 < 2, { apply le_succ },
      rw [ of_nat_succ
         , to_nat_append
         , k_ih
         , bits_to_nat_to_bool
         , mod_pow_succ h],
      ac_refl, }
  end

  protected def to_int : Π {n : nat}, bitvec n → int
  | 0        _ := 0
  | (succ n) v :=
    cond (head v)
      (int.neg_succ_of_nat $ bitvec.to_nat $ not $ tail v)
      (int.of_nat $ bitvec.to_nat $ tail v)

end conversion

private def repr {n : nat} : bitvec n → string
| ⟨bs, p⟩ :=
  "0b" ++ (bs.map (λ b : bool, if b then '1' else '0')).as_string

instance (n : nat) : has_repr (bitvec n) :=
⟨repr⟩
end bitvec

instance {n} {x y : bitvec n} : decidable (bitvec.ult x y) := bool.decidable_eq _ _
instance {n} {x y : bitvec n} : decidable (bitvec.ugt x y) := bool.decidable_eq _ _

import .common

namespace x86

------------------------------------------------------------------------
-- Notation

open mc_semantics
open mc_semantics.type
open reg
open semantics

notation `pattern` body `pat_end` := mk_pattern body

-- Introduces notation x[h..l] to slice the h..l bits out of x.
local notation x `[[`:1025 h `..` l `]]` := slice x h l

local infix ≠ := neq

local notation `⇑`:max x:max := coe1 x

local notation ℕ := nat_expr

infix `.=`:20 := set

------------------------------------------------------------------------
-- utility functions

def msb {w:ℕ} (v : bv w) : bit := sorry
def is_zero {w:ℕ} (v : bv w) : bit := sorry
def least_byte {w:ℕ} (v : bv w) : bv 8 := sorry
def even_parity {w:ℕ} (v : bv w) : bit := sorry

def set_undefined {tp:type} (v : lhs tp) : semantics unit := do
  semantics.add_action (action.mk_undef v)

def set_overflow (b:bit) : semantics unit := do
  cf .= b,
  of .= b,
  set_undefined sf,
  set_undefined zf,
  set_undefined af,
  set_undefined pf

def set_result_flags {w:ℕ} (res : expression (bv w)) : semantics unit := do
  sf .= msb res,
  zf .= is_zero res,
  pf .= even_parity (least_byte res)

def set_bitwise_flags {w:ℕ} (res : expression (bv w)) : semantics unit := sorry

def ssub_overflows  {w:ℕ} (dest : expression (bv w)) (src : expression (bv w)) : bit := sorry
def usub4_overflows {w:ℕ} (dest : expression (bv w)) (src : expression (bv w)) : bit := sorry
def usub_overflows  {w:ℕ} (dest : expression (bv w)) (src : expression (bv w)) : bit := sorry

def uadd_overflows  {w:ℕ} (dest : expression (bv w)) (src : expression (bv w)) : bit := sorry
def uadd4_overflows {w:ℕ} (dest : expression (bv w)) (src : expression (bv w)) : bit := sorry
def sadd_overflows  {w:ℕ} (dest : expression (bv w)) (src : expression (bv w)) : bit := sorry

def uadc_overflows  {w:ℕ} (dest : expression (bv w)) (src : expression (bv w)) (carry : expression bit) : bit := sorry
def uadc4_overflows {w:ℕ} (dest : expression (bv w)) (src : expression (bv w)) (carry : expression bit) : bit := sorry
def sadc_overflows  {w:ℕ} (dest : expression (bv w)) (src : expression (bv w)) (carry : expression bit) : bit := sorry

def do_cmp {w:ℕ} (x : expression (bv w)) (y : expression (bv w)) : semantics unit := do
  of .= ssub_overflows x y,
  af .= usub4_overflows x y,
  cf .= usub_overflows x y,
  set_result_flags (x - y)

def nat_expr_to_bv {w:ℕ} (x : ℕ) : bv w := sorry

def push {w: one_of [8, 16, 32, 64]} (value : expression (bv w)) : semantics unit := do
  rsp .= ⇑rsp - (nat_expr_to_bv (one_of.to_nat_expr w)),
  ⇑rsp .= uext value 64,
  return ()

-- def pop (w: one_of [8,16,32,64]) : semantics (expression (bv w)) := do
def pop (w: ℕ) : semantics (bv w) := do
  temp ← eval ⇑rsp,
  rsp .= ⇑rsp + (nat_expr_to_bv w),
  return (uext temp w)

def do_jmp (cond : bool) (addr : expression (bv 64)) : semantics unit :=
  match cond with
  | tt := record_event (event.jmp addr)
  | _  := pure ()
  end

def do_xchg {w:ℕ} (addr1 : bv w) (addr2 : bv w) : semantics unit :=
  record_event (event.xchg addr1 addr2)

-- `off` is the index of the bit to return.
-- TODO: figure out how to handle out of bounds and any other edge cases and document the
-- assumptions.
def bv_bit {w:ℕ} (base : bv w) (off : bv w) : bit := sorry
def bv_xor {w:ℕ} (x : bv w) (y : bv w) : bv w := sorry
def bv_shl {w:ℕ} (b : bv w) (y : bv w) : bv w := sorry
def bv_complement {w:ℕ} (b : bv w) : bv w := sorry
def bv_is_zero {w:ℕ} (b : bv w) : bit := sorry
def bv_and {w:ℕ} (x : expression (bv w)) (y : expression (bv w)) : expression (bv w) := sorry
def bv_or  {w:ℕ} (x : expression (bv w)) (y : expression (bv w)) : expression (bv w) := sorry
def bv_to_nat {w:ℕ} (x : bv w) : nat := sorry
def bv_cat {w:ℕ} (x : bv w) (y : bv w) : bv (2*w) := sorry

infixl `.|.`:65 := bv_or
infixl `.&.`:70 := bv_and

------------------------------------------------------------------------
-- imul definition

def imul : instruction :=
 definst "imul" $ do
   pattern λ(src : bv 8), do
     tmp ← eval $ sext (⇑al) 16 * sext src _,
     ax .= tmp,
     set_overflow $ sext tmp[[7..0]] _ ≠ tmp
   pat_end,
   pattern λ(src : bv 16), do
     tmp ← eval $ sext (⇑ax) 32 * sext src _,
     dx .= tmp[[31..16]],
     ax .= tmp[[15.. 0]],
     set_overflow $ sext tmp[[15..0]] _ ≠ tmp
   pat_end,
   pattern λ(src : bv 32), do
     tmp ← eval $ sext ⇑eax 64 * sext src _,
     edx .= tmp[[63..32]],
     eax .= tmp[[31.. 0]],
     set_overflow $ sext tmp[[31..0]] _ ≠ tmp
   pat_end,
   pattern λ(w : one_of [8,16,32,64]) (dest : lhs (bv w)) (src : bv w), do
     tmp     ← eval $ sext ⇑dest (2*w) * sext src (2*w),
     tmp_low ← eval $ trunc tmp w,
     dest .= tmp_low,
     set_overflow $ sext tmp_low (2*w) ≠ tmp
   pat_end,
   pattern λ(w : one_of [16,32,64]) (dest : lhs (bv w)) (src1 src2 : bv w), do
     tmp     ← eval $ sext ⇑src1 (2*w) * sext src2 (2*w),
     tmp_low ← eval $ trunc tmp w,
     dest .= tmp_low,
     set_overflow $ sext tmp_low (2*w) ≠ tmp
   pat_end

------------------------------------------------------------------------
-- mul definition

def mul : instruction := do
 definst "mul" $ do
   pattern λ(src : bv 8), do
     tmp ← eval $ uext ⇑al 16 * uext src 16,
     ax .= tmp,
     set_overflow $ tmp[[16..8]] ≠ 0
   pat_end,
   pattern λ(src : bv 16), do
     tmp ← eval $ uext (⇑ax) 32 * uext src _,
     dx .= tmp[[31..16]],
     ax .= tmp[[15.. 0]],
     set_overflow $ tmp[[31..16]] ≠ 0
   pat_end,
   pattern λ(src : bv 32), do
     tmp ← eval $ uext ⇑eax 64 * uext src _,
     edx .= tmp[[63..32]],
     eax .= tmp[[31.. 0]],
     set_overflow $ tmp[[63..32]] ≠ 0
   pat_end,
   pattern λ(src : bv 64), do
     tmp ← eval $ uext ⇑rax 128 * uext src _,
     rdx .= tmp[[127..64]],
     rax .= tmp[[63 .. 0]],
     set_overflow $ tmp[[127..64]] ≠ 0
   pat_end

------------------------------------------------------------------------
-- mov definition

def mov : instruction := do
 definst "mov" $ do
   pattern λ(w : one_of [8,16,32,64]) (dest : lhs (bv w)) (src : bv w), do
     dest .= src
   pat_end

------------------------------------------------------------------------
-- mov definition
-- Move Data from String to String

def movs : instruction := do
 definst "movs" $ do sorry

------------------------------------------------------------------------
-- movsx definition
-- Move with Sign-Extension

def movsx : instruction := do
 definst "movsx" $ do
   pattern λ(w : one_of [16,32,64]) (u : one_of [8, 16]) (dest : lhs (bv w)) (src : bv u), do
     dest .= sext src w
   pat_end

------------------------------------------------------------------------
-- movsxd definition
-- Move with Sign-Extension

def movsxd : instruction := do
 definst "movsxd" $ do
   pattern λ(w : one_of [16,32,64]) (u : one_of [16, 32]) (dest : lhs (bv w)) (src : bv u), do
     dest .= sext src w
   pat_end

------------------------------------------------------------------------
-- movzx definition
-- Move with Zero-Extend

def movzx : instruction := do
 definst "movzx" $ do
   pattern λ(w : one_of [16,32,64]) (u : one_of [8, 16]) (dest : lhs (bv w)) (src : bv u), do
     dest .= uext src w
   pat_end

------------------------------------------------------------------------
-- xchg definition
-- Exchange Register/Memory with Register
def xchg : instruction := do
 definst "xchg" $ do
   pattern λ(w : one_of [8,16,32,64]) (dest : lhs (bv w)) (src : lhs (bv w)), do
     do_xchg ⇑dest ⇑src
   pat_end

------------------------------------------------------------------------
-- cmps definition
-- Compare String Operands

def cmps : instruction := do
 definst "cmps" $ sorry
   --pattern λ(w : one_of [8,16,32,64]) (dest : bv w) (src : bv w)
   --pat_end

------------------------------------------------------------------------
-- cmp definition
-- Compare Two Operands

def cmp : instruction := do
 definst "cmp" $ do
   pattern λ(u v : one_of [8,16,32,64]) (src1 : bv u) (src2 : bv v), do
     do_cmp src1 (sext src2 u)
   pat_end

------------------------------------------------------------------------
-- dec definition
-- Decrement by 1

def dec : instruction := do
 definst "dec" $ do
   pattern λ(w : one_of [8,16,32,64]) (value : lhs (bv w)), do
     temp ← eval $ ⇑value - 1,
     of .= ssub_overflows temp 1,
     af .= usub4_overflows temp 1,
     set_result_flags temp,
     value .= temp
   pat_end

------------------------------------------------------------------------
-- div definition
-- Unsigned Divide

def div : instruction := do
 definst "div" $ do
   -- TODO: would it be better to have a single div primitive?
   pattern λ(src : bv 8), do
     tempQuot ← eval $ expression.quot ⇑ax (uext src 16),
     tempRem  ← eval $ expression.rem  ⇑ax (uext src 16),
     al .= tempQuot[[7..0]],
     ah .= tempRem[[7..0]]
   pat_end,
   pattern λ(src : bv 16), do
     tempQuot ← eval $ expression.quot (bv_cat ⇑dx ⇑ax) (uext src 32),
     tempRem  ← eval $ expression.rem  (bv_cat ⇑dx ⇑ax) (uext src 32),
     ax .= tempQuot[[15..0]],
     dx .= tempRem[[15..0]]
   pat_end,
   pattern λ(src : bv 32), do
     tempQuot ← eval $ expression.quot (bv_cat ⇑edx ⇑eax) (uext src 64),
     tempRem  ← eval $ expression.rem  (bv_cat ⇑edx ⇑eax) (uext src 64),
     eax .= tempQuot[[31..0]],
     edx .= tempRem[[31..0]]
   pat_end,
   pattern λ(src : bv 64), do
     tempQuot ← eval $ expression.quot (bv_cat ⇑rdx ⇑rax) (uext src 128),
     tempRem  ← eval $ expression.rem  (bv_cat ⇑rdx ⇑rax) (uext src 128),
     rax .= tempQuot[[63..0]],
     rdx .= tempRem[[63..0]]
   pat_end

------------------------------------------------------------------------
-- and definition
-- Logical AND

def and : instruction := do
 definst "and" $ do
   pattern λ(w : one_of [8, 16, 32, 64]) (dest : lhs (bv w)) (src : bv w), do
     tmp ← eval $ ⇑dest .&. src,
     set_bitwise_flags tmp,
     dest .= tmp
   pat_end

------------------------------------------------------------------------
-- bt definition
-- Bit Test

def bt : instruction := do
 definst "bt" $ do
   pattern λ(w : one_of [16, 32, 64]) (base : bv w) (off : bv w), do
     cf .= bv_bit ⇑base off
   pat_end,
   pattern λ(w : one_of [16, 32, 64]) (base : bv w) (off : bv 8), do
     cf .= bv_bit ⇑base (uext off w)
   pat_end

------------------------------------------------------------------------
-- btc definition
-- Bit Test and Complement

def btc : instruction := do
 definst "btc" $ do
   pattern λ(w : one_of [16, 32, 64]) (base : lhs (bv w)) (off : bv w), do
     cf   .= bv_bit ⇑base off,
     base .= bv_xor ⇑base (bv_shl 1 off)
   pat_end,
   pattern λ(w : one_of [16, 32, 64]) (base : lhs (bv w)) (off : bv 8), do
     cf   .= bv_bit ⇑base (uext off w),
     base .= bv_xor ⇑base (uext (bv_shl 1 off) w)
   pat_end

------------------------------------------------------------------------
-- btr definition
-- Bit Test and Reset

def btr : instruction := do
 definst "btr" $ do
   pattern λ(w : one_of [16, 32, 64]) (base : lhs (bv w)) (off : bv w), do
     cf   .= bv_bit ⇑base off,
     base .= ⇑base .&. (bv_complement (bv_shl 1 off))
   pat_end,
   pattern λ(w : one_of [16, 32, 64]) (base : lhs (bv w)) (off : bv 8), do
     cf   .= bv_bit ⇑base (uext off w),
     base .= ⇑base .&. (bv_complement (uext (bv_shl 1 off) w))
   pat_end

------------------------------------------------------------------------
-- bts definition
-- Bit Test and Set

def bts : instruction := do
 definst "bts" $ do
   pattern λ(w : one_of [16, 32, 64]) (base : lhs (bv w)) (off : bv w), do
     cf   .= bv_bit ⇑base off,
     base .= ⇑base .|. (bv_shl 1 off)
   pat_end,
   pattern λ(w : one_of [16, 32, 64]) (base : lhs (bv w)) (off : bv 8), do
     cf   .= bv_bit ⇑base (uext off w),
     base .= ⇑base .|. (uext (bv_shl 1 off) w)
   pat_end

------------------------------------------------------------------------
-- bsf definition
-- Bit Scan Forward

def bsf_def : instruction := do
 definst "bsf" $ do
   pattern λ(w : one_of [16, 32, 64]) (r : lhs (bv w)) (y : bv w), do
     set_undefined cf,
     set_undefined of,
     set_undefined sf,
     set_undefined af,
     set_undefined pf,
     zf .= bv_is_zero y,
     r .= bsf y
  pat_end

------------------------------------------------------------------------
-- bsr definition
-- Bit Scan Reverse

def bsr_def : instruction := do
 definst "bsr" $ do
   pattern λ(w : one_of [16, 32, 64]) (r : lhs (bv w)) (y : bv w), do
     set_undefined cf,
     set_undefined of,
     set_undefined sf,
     set_undefined af,
     set_undefined pf,
     zf .= bv_is_zero y,
     r .= bsr y
  pat_end

------------------------------------------------------------------------
-- bswap definition
-- Byte Swap

def bswap : instruction := do
 definst "bswap" $ do
   pattern λ(w : one_of [32, 64]) (dest : lhs (bv w)), do
     dest .= expression.bswap ⇑dest
   pat_end

------------------------------------------------------------------------
-- add definition

def add : instruction := do
 definst "add" $ do
   pattern λ(w : one_of [8, 16, 32, 64]) (dest : lhs (bv w)) (src : bv w), do
     tmp ← eval $ ⇑dest + src,
     set_result_flags tmp,
     cf .= uadd_overflows tmp src,
     of .= sadd_overflows tmp src,
     af .= uadd4_overflows tmp src,
     dest .= tmp
   pat_end

------------------------------------------------------------------------
-- adc definition
-- Add with Carry

def adc : instruction := do
 definst "adc" $ do
   pattern λ(w : one_of [8, 16, 32, 64]) (dest : lhs (bv w)) (src : bv w), do
     tmp ← eval $ expression.adc ⇑dest src cf,
     set_result_flags tmp,
     cf .= uadc_overflows  tmp src cf,
     of .= sadc_overflows  tmp src cf,
     af .= uadc4_overflows tmp src cf,
     dest .= tmp
   pat_end

------------------------------------------------------------------------
-- xadd definition
-- Exchange and Add

def xadd : instruction := do
 definst "xadd" $ do
   pattern λ(w : one_of [8, 16, 32, 64]) (dest : lhs (bv w)) (src : lhs (bv w)), do
     tmp ← eval $ ⇑dest + ⇑src,
     src .= ⇑dest,
     set_result_flags tmp,
     cf .= uadd_overflows  tmp src,
     of .= sadd_overflows  tmp src,
     af .= uadd4_overflows tmp src,
     dest .= tmp
   pat_end

------------------------------------------------------------------------
-- fadd definition

def fadd : instruction := do
 definst "fadd" $ do
   pattern λ(dest : lhs x86_80) (src : lhs x86_80), do
     dest .= x87_fadd dest src
   pat_end,
   pattern λ(src : lhs float), do
     st0  .= x87_fadd st0 ↑src
   pat_end,
   pattern λ(src : lhs double), do
     st0  .= x87_fadd st0 ↑src
   pat_end

------------------------------------------------------------------------
-- faddp definition

def faddp : instruction := do
 definst "faddp" $ do
   pattern λ(dest : lhs x86_80) (src : lhs x86_80), do
     dest .= x87_fadd dest src,
     record_event event.pop_x87_register_stack
   pat_end

------------------------------------------------------------------------
-- fiadd definition

def fiadd : instruction := do
 definst "fiadd" $ do
   pattern λ(w : one_of [16,32]) (src : lhs (bv w)), do
     st0 .= x87_fadd st0 ↑src
   pat_end

------------------------------------------------------------------------
-- syscall definition

def syscall : instruction :=
  definst "syscall" $ mk_pattern (record_event event.syscall)

------------------------------------------------------------------------
-- lea definition
-- Load Effective Address

def lea : instruction :=
 definst "lea" $ do
   pattern λ(w : one_of [16, 32, 64]) (dest : lhs (bv w)) (src : bv 64), do
     dest .= trunc src w
   pat_end

------------------------------------------------------------------------
-- call definition
-- Call Procedure

def call : instruction :=
 definst "call" $ do
   pattern λ(w : one_of [16, 32, 64]) (v : bv w), do
     record_event (event.call (uext v 64))
   pat_end

------------------------------------------------------------------------
-- jmp definition
-- Jump
def jmp : instruction :=
 definst "jmp" $ do
   pattern λ(w : one_of [8, 16, 32, 64]) (v : bv w), do
     do_jmp true (uext v 64)
   pat_end

------------------------------------------------------------------------
-- ret definition
-- Return from Procedure
def ret : instruction :=
 definst "ret" $ do
   pattern do
     -- pop (one_of.var 64),
     pop 64,
     record_event event.ret
   pat_end,
   pattern λ(off : (bv 16)), do
     -- pop (one_of.var (64 + bv_to_nat off)),
     pop (64 + bv_to_nat off),
     record_event event.ret
   pat_end

------------------------------------------------------------------------
-- pop definition
-- Pop a Value from the Stack
def pop_def : instruction :=
 definst "pop" $ do
   pattern λ(w : one_of [16, 32, 64]) (dest: lhs (bv w)),do
     v ← pop w,
     dest .= v
   pat_end

------------------------------------------------------------------------
-- push definition
-- Push Word, Doubleword or Quadword Onto the Stack
def push_def : instruction :=
 definst "push" $ do
   pattern λ(w : one_of [8, 16, 32, 64]) (value: bv w),do
     push value
   pat_end

------------------------------------------------------------------------
-- cwd definition
-- Convert Word to Doubleword
def cwd : instruction :=
 definst "cwd" $ do
   pattern do
     let doubleword := sext ⇑ax 32, do
     dx .= doubleword[[31..16]]
   pat_end

------------------------------------------------------------------------
-- cdq definition
-- Convert Doubleword to Quadword
def cdq : instruction :=
 definst "cdq" $ do
   pattern do
     let quadword := sext ⇑eax 64, do
     edx .= quadword[[63..32]]
   pat_end

------------------------------------------------------------------------
-- cqo definition
-- Convert Quadword to Octword
def cqo : instruction :=
 definst "cqo" $ do
   pattern do
     let octword := sext ⇑rax 128, do
     rdx .= octword[[127..64]]
   pat_end

------------------------------------------------------------------------
-- cbw definition
-- Convert Byte to Word
def cbw : instruction :=
 definst "cbw" $ do
   pattern do
     ax .= sext ⇑al 16
   pat_end

------------------------------------------------------------------------
-- cwde definition
-- Convert Word to Doubleword
def cwde : instruction :=
 definst "cwde" $ do
   pattern do
     eax .= sext ⇑ax 32
   pat_end

------------------------------------------------------------------------
-- cwde definition
-- Convert Doubleword to Quadword
def cdqe : instruction :=
 definst "cdqe" $ do
   pattern do
     rax .= sext ⇑eax 64
   pat_end

------------------------------------------------------------------------
-- clc definition
-- Clear Carry Flag
def clc : instruction :=
 definst "clc" $ do
   pattern do
     cf .= zero
   pat_end

------------------------------------------------------------------------
-- cld definition
-- Clear Direction Flag
def cld : instruction :=
 definst "cld" $ do
   pattern do
     df .= zero
   pat_end

end x86

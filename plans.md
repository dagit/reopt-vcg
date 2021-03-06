The VADD VCG consists of the following components:

1. A data structure for representing the relationships between machine code and
   LLVM identified by reopt along with a parser for said data structure.  The
   information included will include:
   - The address of each LLVM function in the original binary.
   - The correspondance between each basic block in the LLVM, and the binary address.
   - Other information that will need to be determined.
2. An API for generating SMTLIB, and writing it to file handles.
3. A **loader** API for parsing a static elf binary, and providing an interface
  to infer the state of memory after loading the code.
  3.1 The state of memory will include code and initial data segment locations
       and contents.
4. A data type for representing x86_64 instructions along with:

   4.1. A machine code disassembler for converting bytes into the
    instruction representation for the data type.

   4.2. An assembly parser for translating inline assembly into the data type.

   Note that because of requirements 4.1 and 4.2, we need to ensure that the data
   type is sufficiently flexible that it can accomodate both of these things.

5. A machine code semantics for translating the x86_64 instructions into a simpler
   register transfer language that precisely captures the semantics effects of the
   instructions on the processor state.

6. A machine code symbolic translator that accepts an address and code segment
   contents, and outputs a sequence of **events** that the code would
   perform when executing the code at that address.
   - The events will include SMTLIB declarations for representing
     expressions generated by computations.
   - It will also include side effects like system or function calls.
   - The symbolic translator will stop after it encounters an instruction
     that modifies control flow in some way.

7. A data type for representing LLVM modules along with a parsing capability for turning
   `.bc` files into LLVM modules.

   - We will likely reuse the existing LLVM compiler bitcode parser.

8. An LLVM machine code translator similar to (6), but with events tailored
   to LLVM.

9. A event comparator that compares events in machine code and LLVM, and generates
   SMTLIb sufficient to prove the LLVM events refine the machine code events.
   - The comparator will be able to generate standalone files, and interactively
     query an SMT solver.

10. A program that uses the above components to provide a command-line VCG.

These are needed for implementing the VCG.  To verify the correctness,
we will need additional capabilities:
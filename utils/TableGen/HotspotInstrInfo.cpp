//===- HotspotInstrInfoEmitter.cpp - Generate a Instruction Set Desc. ------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This tablegen backend is responsible for emitting a description of the target
// instruction set for the code generator.
//
//===----------------------------------------------------------------------===//


#include "CodeGenDAGPatterns.h"
#include "CodeGenSchedule.h"
#include "CodeGenTarget.h"
#include "SequenceToOffsetTable.h"
#include "TableGenBackends.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/TableGen/Error.h"
#include "llvm/TableGen/Record.h"
#include "llvm/TableGen/TableGenBackend.h"
#include <algorithm>
#include <cstdio>
#include <string>
#include <map>
#include <vector>
#include <iomanip>

using namespace llvm;

#define StrEq(a,b) ( a.compare(b)==0 )

#define D OS << "At line: " << __LINE__ << "\n"; OS.flush();

#define E(x) OS << "At line: " << __LINE__ <<  " " << #x << " " << x <<  "\n"; OS.flush();


//#define DEBUG_PRINTS_HOTSPOT_INST_GENERATOR


// This code makes Assembler::instruction(..) methods 
// for Hotspot out of tablegen records
// to be used in Hotspot for ports to new platforms


// Known issues:
// * Can not handle ranges. When a 12-bit immediate is encoded into instruction
//     as bits 0..3 and 8..15. Reported as # of instructions with weared encodings
// * Need to understand and handle types like DPR, QPR
// * process bit initializers
// * failures methods starting with s && t



namespace {

  class ValueEncoding {
     std::vector<unsigned> starting_bit; 
     std::vector<unsigned> ending_bit;
     unsigned total_encoding_bits;
     
    
  };
  
  class HotspotInstrInfoEmitter {
    RecordKeeper &Records;
    CodeGenDAGPatterns CDP;
    const CodeGenSchedModels &SchedModels;

  public:

    HotspotInstrInfoEmitter(RecordKeeper &R) :
    Records(R), CDP(R), SchedModels(CDP.getTargetInfo().getSchedModels()) {
    }

    // run - Output the instruction set description.
    void run(raw_ostream &OS);

  private:
  };
} // End anonymous namespace

static void PrintDefList(const std::vector<Record*> &Uses,
        unsigned Num, raw_ostream &OS) {
  OS << "static const uint16_t ImplicitList" << Num << "[] = { ";
  for (unsigned i = 0, e = Uses.size(); i != e; ++i)
    OS << getQualifiedName(Uses[i]) << ", ";
  OS << "0 };\n";
}

//===----------------------------------------------------------------------===//
// Main Output.
//===----------------------------------------------------------------------===//

// run - Emit the main instruction description records for the target...

void HotspotInstrInfoEmitter::run(raw_ostream &OS) {
  emitSourceFileHeader("Target Instructions", OS);

  OS << "\n#ifdef GET_HOTSPOTINFO_MC_DESC\n";
  OS << "#undef GET_HOTSPOTINFO_MC_DESC\n";

  OS << "namespace llvm {\n\n";

  CodeGenTarget &Target = CDP.getTargetInfo();
  const std::string &TargetName = Target.getName();
  Record *InstrInfo = Target.getInstructionSet();

  // Keep track of all of the def lists we have emitted already.
  std::map<std::vector<Record*>, unsigned> EmittedLists;
  unsigned ListNumber = 0;
  std::vector<std::string> troubled_records;
  int total=0;
  int good=0;
  int nr_inst_with_broken_encodings=0;

  // Emit all of the instruction's implicit uses and defs.
  for (const CodeGenInstruction *II : Target.instructions()) {
    
    total++;
    Record *Inst = II->TheDef;
    std::vector<Record*> Uses = Inst->getValueAsListOfDefs("Uses");
    unsigned input_registers = 0;
    unsigned output_registers = 0;
    unsigned immed = 0;

    if (Inst->isValueUnset("NAME")) continue;
    auto name = Inst->getValueAsString("NAME");

    // TODO: troubles with instructions starting with t
    if (name[0]=='t') {
      OS << "//Exclusion of instruction record "
              << name 
              << ". \n//due to knon issues with instructions that start with 't'\n\n";
      continue;
    }
    if (name[0]=='s') {
      OS << "//Exclusion of instruction record "
              << name 
              << ". \n//due to knon issues with instructions that start with 's'\n\n";
      continue;
    }
    
    //#ifdef DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
    //OS << "Record: " << *Inst << "\n\n\n";
    //#endif // DEBUG_PRINTS_HOTSPOT_INST_GENERATOR

#define SKIP_RECORD(R) if (name.compare(#R)==0) continue;


    // this check borrowed from void FixedLenDecoderEmitter::run(..)
    unsigned Size = Inst->getValueAsInt("Size");
    if (Inst->getValueAsString("Namespace") == "TargetOpcode" ||
        Inst->getValueAsBit("isPseudo") ||
        Inst->getValueAsBit("isAsmParserOnly") ||
        Inst->getValueAsBit("isCodeGenOnly")) {
      
      OS << "//Proper exclusion of instruction record "
              << name 
              << ". \n//Not part of the actual instruction set\n\n";
      continue;
    }





    BitsInit* bi = Inst->getValueAsBitsInit("Inst");

    // Not found or incomplete
    if ((!bi) || (bi->allInComplete())) {
      OS << "//Proper exclusion of instruction record "
              << name 
              << ". \n//The Inst Record is not found or incomplete\n\n";
      continue;
    }

    if (bi->getNumBits() != 32 ) {
      OS << "//We can't handle yet instructions with encodings other that 32-bit\n"
              << "//therefore skipping instruction record "
              << name 
              << "\n\n";
      continue;
    }

    std::vector<std::pair<Init*, std::string> > InOutOperands;
    DagInit *Out = Inst->getValueAsDag("OutOperandList");
    DagInit *In = Inst->getValueAsDag("InOperandList");


    // This should really be a 3-element std::tuple
    std::vector<std::string> arg_names;
    std::vector<unsigned> arg_sizes;
    std::vector<unsigned> start_positions;
    std::vector<std::string> type_names;
    bool error_while_parsing=false;
    std::string error_msg;
    int start_of_in_args=0;

      // OK, now we process DAG of output arguments. 
      // Should be 0 or 1 but who knows..
      // We want to know names and (if possible) sizes

    for (unsigned i = 0; i < Out->getNumArgs(); ++i) {
      const std::string &aname = Out->getArgName(i);
      InOutOperands.push_back(std::make_pair(Out->getArg(i), aname));

#ifdef DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
      OS << "Found #" << i + 1 << " in argument with name " << aname << "\n";
#endif //DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
      BitsInit *arg_bits_int;
      if ((Inst->getValue(aname))
          && (arg_bits_int = Inst->getValueAsBitsInit(aname))) {
#ifdef DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
        OS << "with length " << arg_bits_int->getNumBits() << " bits\n";
#endif // DEBUG_PRINTS_HOTSPOT_INST_GENERATOR  
        arg_sizes.push_back(arg_bits_int->getNumBits());
      } else {
#ifdef DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
        OS << " (but BitsInit struct not found\n";
#endif // DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
        arg_sizes.push_back(-1);
      }
      arg_names.push_back(aname);
      start_positions.push_back(-1); //uninitialized

      // Stupid assumption that if there is a destination element - it is a reg
      type_names.push_back("Register");
    }  // for all output arguments


      // OK, now we process DAG of input arguments. 
      // We want to know names and (if possible) sizes
    
    start_of_in_args= arg_names.size();

    for (unsigned i = 0; i < In->getNumArgs(); ++i) {
      
      if (error_while_parsing) break;
      
      const std::string &aname = In->getArgName(i);
      
      if (aname.empty()) {
        // No name for VarArg, see EORrsr for example

        // We still will try to generate such instruction
        error_while_parsing=true;
        
        continue;
      }
      if StrEq(aname,"s")  { 
        // we deliberately omit the cc_out argument
        // see comments in ARMAsmParser::shouldOmitCCOutOperand
        // This is not needed for the current prototype

        // in this context ignoring means "set corresponding bit to 0"
#ifdef DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
        OS << "// Instruction with the cc_out argument detected\n"
                << "// and this bit was discarded. This instruction encoding\n"
                << "// may require a fixup. The cc_out bit position is "
                << i << "\n";
#endif // DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
        OS << "//We can't handle yet instructions with s-bit (cc_out bit)\n"
              << "//therefore skipping instruction record "
              << name 
              << "\n\n";
        error_while_parsing=true;
        continue;
      } // end of a check fro "s"

#ifdef DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
      OS << "inarg - " << In->getArg(i)->getAsString();
#endif // DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
      std::string type_name = In->getArg(i)->getAsString();

      // Let's detect the type of a given input argument
      if StrEq(type_name,"so_reg_reg") {
        type_names.push_back("ShiftRegister");
      } else {
        if StrEq(type_name,"so_reg_imm") {
          type_names.push_back("ShiftImmediate");
        } else {
          if StrEq(type_name,"mod_imm") {
            type_names.push_back("Immediate");
          } else {
            if StrEq(type_name,"QPR") {
              OS << "//We can't handle yet instructions with QPR regs as imuts\n"
                    << "//therefore skipping instruction record "
                    << name 
                    << "\n\n";
              // Don't know how to handle these
              error_while_parsing=true;
              continue;
            } else {
              // Both for register and immediates. Is it right?
              type_names.push_back("Register");
            }
          }
        }
      }// outermost "if-else" for finding type of argument
      
      // OK, now we process DAG of input arguments
      // We want to know names and (if possible) sizes


      InOutOperands.push_back(std::make_pair(In->getArg(i), aname));
#ifdef DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
      OS << "Found #" << i + 1 << " in argument with name " << aname << " ";
#endif // DEBUG_PRINTS_HOTSPOT_INST_GENERATOR

      BitInit *arg_bit_init;
      BitsInit *arg_bits_int;
      bool val;
      
      // May be it is just a bit ? (Rare)
      if ((Inst->getValue(aname))
          && ( (arg_bit_init = dyn_cast<BitInit>(Inst->getValueInit(aname)))
                
                // Dirty hack. I just don't know what to how to check
                // that a field is of a BitInit type
                || StrEq(aname,"lane"))) {
        //#ifdef DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
        OS << "with length 1 bit\n";
        //#endif // DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
        arg_sizes.push_back(1); // size is just 1 bit
      } else {
      // May be it is a list of var bits ? (Common)
        if ((Inst->getValue(aname))
            && (arg_bits_int = Inst->getValueAsBitsInit(aname))) {
#ifdef DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
          OS << "with length " << arg_bits_int->getNumBits() << " bits\n";
#endif // DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
          arg_sizes.push_back(arg_bits_int->getNumBits());
        } else {
#ifdef DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
          OS << " (but BitsInit struct not found\n";
#endif // DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
          arg_sizes.push_back(-1); //uninitialized
        }
      }
      arg_names.push_back(aname);
      start_positions.push_back(-1); //uninitialized
    }
    
    if (error_while_parsing) {
      // Some error was detected earlier
      // We already printed diagnostics
      // Need to go now to the next instruction record
      continue;
    }


    // OK, now we know all in/out arguments names and sizes (perhaps))
    // Time to find out where those arguments should be encoded 
    // in an instruction.
    // This is done by walking the "Inst" list
    // Along the way we will reconstruct the opcode     


    // accum is where we store opcode and other constant in this instruction
    unsigned int accum = 0;
    
    
    // Walk the Inst list in the current record
    
    int number_of_bits=bi->getNumBits();
    for (int i = 0; i < bi->getNumBits(); i++) {

      if (VarBitInit::classof(bi->getBit(i))) {
        
        // let's try parameters first
        VarBitInit *Bp = dyn_cast<VarBitInit>(bi->getBit(i));
        
        // One or several letters corresponding to the bit in Inst struct
        const std::string n = Bp->TI->getAsString();

        int j = 0;
        bool record_found;

        for (j=0;j<arg_names.size();j++) {
          if StrEq(arg_names[j],n) {
            // Found a matching name, let's record from what byte encoding starts
            start_positions[j] = i;
                        
            // Let's find how many consecutive bits denoted with string n 
            int z=i-1;
            std::string m;
            do { 
              z++;
              VarBitInit *Bpp = dyn_cast<VarBitInit>(bi->getBit(z));
              if (Bpp) 
                m = Bpp->TI->getAsString();
              else
                // No VarBitInit means no name 
                //   and that means different name from 'n'
                //     therefore so we found the end of sequence
                m="";
            } while ( StrEq(n,m) && ( z < (number_of_bits-1) ) );
           
            // z should always point to the first bit after the sequence
            if (StrEq(n,m)) z++; 
           
            if ( arg_sizes[j] == -1) {
              // Still OK, the length was not known
              arg_sizes[j] = (z-i+1);
            }
           
            if (arg_sizes[j] != (z-i)) {
              // something is wrong with instruction encoding
              // We don't know to parse such ones
              
              OS << "// Instruction "
                      << name
                      << " has parameter "
                      << n
                      <<" encoding that we can not handle\n"
                      "// namely this: "
                      << *bi
                      << "\n"
                      << "// (start position "
                      << start_positions[j]
                      << ". detected size:"
                      << (z-i)
                      << " versus expected "
                      << arg_sizes[j]
                      << ")\n\n";
              nr_inst_with_broken_encodings++;
              error_while_parsing=true;
            }           
            
            if ( (arg_sizes[j] + start_positions[j]) > 32) {
              
              // This is actually a programmatic error 
              
              OS << "// Instruction has parameter "
                      << n
                      <<" encoding that we can not handle. Exceeding inst size\n"
                      "// namely this: "
                      << *bi
                      << "\n"
                      << "// (start position "
                      << start_positions[j]
                      << ". detected size:"
                      << (z-i)
                      << " versus expected "
                      << arg_sizes[j]
                      << "\n\n";
              error_while_parsing=true;
            }
            i+=arg_sizes[j]-1;
          }
          if (error_while_parsing) break;
          
        } // for all known param names
        
        if (error_while_parsing) break;
        continue;
        
      } // if current bit is a var bit

      // capture constants in the instruction description
      BitInit *B = dyn_cast<BitInit>(bi->getBit(i));
      if (!B) continue;

      // is llvm::Init::InitKind.IK_BinOpInit
      if ((B->getKind() == 0) && (B->getValue())) {
        accum += (1 << i);
      }


    } //for bits


    if (error_while_parsing) {
      // Some error was detected earlier
      // We already printed diagnostics
      // Need to go now to the next instruction record
      continue;
      
    }


    // ==================================
    // Print method name and parameters (skipping out args))
    OS << "void Assembler::"
            << name;
    for (int j = start_of_in_args; j < arg_names.size(); j++) {
      if (j == Out->getNumArgs()) OS << "_";
      OS << arg_names[j][0];
    }
    OS << "(";

    for (int j = 0; j < arg_names.size(); j++) {

      if (j > 0) OS << ", ";
      OS << type_names[j] << " " << arg_names[j];
    }
    OS << ") {\n";

    // ==================================
    // Encode opcode

    OS << "  uint32 instr_enc=0x";
    OS.write_hex(accum);
    OS << ";\n";

    // ==================================
    // Encode parameters
    for (int j = 0; j < arg_names.size(); j++) {

      if (arg_sizes[j] == -1) {
        OS << "  // Error while parsing record " << name << "\n";
        // Save the "bad record"
        troubled_records.push_back(name);
        // No reason to encode instruction further
        break;
      }
      
      if (start_positions[j] == -1) {

        // Skip parameter j in emition since it was not found in the encoding
        continue;
      }

      OS << "  instr_enc |= ("
              << arg_names[j]
              << ".value()"
              << " & ((1 << "
              << arg_sizes[j]
              << ") - 1 ))";
      if (start_positions[j])
        OS << " << "
              << start_positions[j];
      OS << ";\n";
    }
    // ==================================
    // Emit intruction and exit
    OS << "  emit_arith(instr_enc);\n}\n\n";

    good++;


#if 0    
    if (!Uses.empty()) {
      unsigned &IL = EmittedLists[Uses];
      if (!IL) PrintDefList(Uses, IL = ++ListNumber, OS);
    }
    std::vector<Record*> Defs = Inst->getValueAsListOfDefs("Defs");
    if (!Defs.empty()) {
      unsigned &IL = EmittedLists[Defs];
      if (!IL) PrintDefList(Defs, IL = ++ListNumber, OS);
    }
#endif 

  } //for Instructions

  

  OS << "} // End namespace llvm\n";

  OS << "\n\n// Total instruction records: " << total<<"\n";  
  OS << "// Emitted methods: " << good<<"\n";  
  OS << "// Number of instructions that were discarded because of weared encoding: "
          << nr_inst_with_broken_encodings << "\n";
  int errors=(int)troubled_records.size();
  /*
   * if (errors) {
      OS << "//These "<<errors<<" instructions gave following troubles: "
              <<"\n//  an input param is of unknown length or at unknown positions:\n";  
    for (int i=0; i< troubled_records.size(); i++) {
      OS << "  " << troubled_records[i] << "\n";  
    }
  }
   */
  

}

namespace llvm {

  void EmitHotspotInstrInfo(RecordKeeper &RK, raw_ostream &OS) {
    HotspotInstrInfoEmitter(RK).run(OS);
    //EmitMapTable(RK, OS);
  }

} // End llvm namespace

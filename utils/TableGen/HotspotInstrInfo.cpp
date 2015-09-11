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

//#define DEBUG_PRINTS_HOTSPOT_INST_GENERATOR


// This code makes Assembler::instruction(..) methods 
// for Hotspot out of tablegen records
// to be used in Hotspot for ports to new platforms


// Known issues:
// * Can not handle ranges. When a 12-bit immediate is encoded into instruction
//     as bits 0..3 and 8..15. We do not even detect this situation!
// * Need to understand and handle types like DPR, QPR
// * process bit initializers
// * failures methods starting with s && t
// * failures methods starting with s && t
// * check that instruction is not 32-bit encoded



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


    for (unsigned i = 0; i < In->getNumArgs(); ++i) {
      const std::string &aname = In->getArgName(i);
      if (aname.empty()) {
        // No name for VarArg, see EORrsr for example
        continue;
      }
      if (aname.compare("s") == 0) {
        // we delibertly omit the cc_out argument
        // see comments in ARMAsmParser::shouldOmitCCOutOperand
        // This is not needed for the current prototype

        // in this context ignoring means "set corresponding bit to 0"
#ifdef DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
        OS << "// Instruction with the cc_out argument detected\n"
                << "// and this bit was discarded. This instruction encoding\n"
                << "// may require a fixup. The cc_out bit position is "
                << i << "\n";
#endif // DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
        continue;
      } // end of a check fro "s"

#ifdef DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
      OS << "inarg - " << In->getArg(i)->getAsString();
#endif // DEBUG_PRINTS_HOTSPOT_INST_GENERATOR
      std::string type_name = In->getArg(i)->getAsString();

      // Let's detect the type of a given input argument
      if (type_name.compare("so_reg_reg") == 0) {
        type_names.push_back("ShiftRegister");
      } else {
        if (type_name.compare("so_reg_imm") == 0) {
          type_names.push_back("ShiftImmediate");
        } else {
          if (type_name.compare("mod_imm") == 0) {
            type_names.push_back("Immediate");
          } else {
            if (type_name.compare("QPR") == 0) {
              // Don't know how to handle these
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
                || (aname.compare("lane")==0))) {
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

    // OK, now we know all in/out arguments names and sizes
    // Time to find out where those arguments should be encoded 
    // in an instruction.
    // This is done by walking the "Inst" list
    // Along the way we will reconstruct the opcode     


    unsigned int accum = 0;
    for (int i = 0; i < bi->getNumBits(); i++) {
      if (VarBitInit::classof(bi->getBit(i))) {
        // let's try parameters first
        VarBitInit *Bp = dyn_cast<VarBitInit>(bi->getBit(i));
        const std::string n = Bp->TI->getAsString();

        int j = 0;
        for (std::vector<std::string>::const_iterator it = arg_names.begin();
             it != arg_names.end();
             j++, it++) {
          if (it->compare(n) == 0) {
            
            // Found a matching name, let's record from what byte encoding starts
            start_positions[j] = i;
          }
        }
        continue;
      }

      // capture constants in the instruction description
      BitInit *B = dyn_cast<BitInit>(bi->getBit(i));
      if (!B) continue;

      // is llvm::Init::InitKind.IK_BinOpInit
      if ((B->getKind() == 0) && (B->getValue())) {
        accum += (1 << i);
      }


    } //for bits




    // ==================================
    // Print method name and parameters
    OS << "void Assembler::"
            << name;
    for (int j = Out->getNumArgs(); j < arg_names.size(); j++) {
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

      if ((arg_sizes[j] == -1) || (start_positions[j] == -1)) {

        OS << "  // Error while parsing record " << name << "\n";
        // Save the "bad record"
        troubled_records.push_back(name);
        // No reason to encode instruction further
        break;
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
  OS << "// Emitted methods (including faulty ones): " << good<<"\n";  
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

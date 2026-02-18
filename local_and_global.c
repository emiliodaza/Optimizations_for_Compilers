#include <stdio.h>
#include <stdbool.h>
#include <llvm-c/Core.h>
#include <vector>
#include <unordered_set>
#include <unordered_map>

bool run_common_subexpression_elimination(LLVMBasicBlockRef bb);
bool run_constant_folding(LLVMBasicBlockRef bb);
bool run_dead_code_elimination(LLVMValueRef func);
bool is_store_in_between_shared_memory_uses(LLVMValueRef first_instruction, LLVMValueRef second_instruction);
std::unordered_set <LLVMValueRef> compute_gen_set_for_block(LLVMBasicBlockRef bb);
std::unordered_set <LLVMValueRef> set_of_all_store (LLVMValueRef func);
std::unordered_set <LLVMValueRef> compute_kill_set_for_block(LLVMBasicBlockRef bb);
struct IN_and_OUT {
    std::unordered_set <LLVMValueRef> in_set;
    std::unordered_set <LLVMValueRef> out_set;
} IN_and_OUT;

int main(){

}
// functions created for local tasks of optimization

bool run_common_subexpression_elimination(LLVMBasicBlockRef bb){
    bool replacement_has_happened = false;
    // If we find that a instruction is repeated we substitute the later
    //  reference with the first one so 
    // that dead code elimination later simplifies the code
    for (LLVMValueRef ins_1 = LLVMGetFirstInstruction(bb); ins_1 != NULL; ins_1 = LLVMGetNextInstruction(ins_1)) {

        for (LLVMValueRef ins_2 = LLVMGetNextInstruction(ins_1); ins_2 != NULL;) {

            LLVMValueRef ins_2_next = LLVMGetNextInstruction(ins_2);
            LLVMOpcode type_of_ins_1 = LLVMGetInstructionOpcode(ins_1);

            if (type_of_ins_1 == LLVMGetInstructionOpcode(ins_2) && (type_of_ins_1 == LLVMAdd || type_of_ins_1 == LLVMMul || type_of_ins_1 == LLVMSub)) {

                LLVMOpcode shared_type_of_ins = type_of_ins_1;
                bool operands_are_the_same_in_order = (LLVMGetOperand(ins_1, 0) == LLVMGetOperand(ins_2, 0) && LLVMGetOperand(ins_1, 1) == LLVMGetOperand(ins_2, 1));
                bool operands_are_the_same_in_opposite_order = (LLVMGetOperand(ins_1, 0) == LLVMGetOperand(ins_2, 1) && LLVMGetOperand(ins_1, 1) == LLVMGetOperand(ins_2, 0));
                bool operands_are_communitatively_the_same = (operands_are_the_same_in_order || operands_are_the_same_in_opposite_order);

                // b/c addition and multiplication are commutative so they are the same subexpression if the sets with operands in the instructions are equal
                if (operands_are_communitatively_the_same && (shared_type_of_ins == LLVMAdd || shared_type_of_ins == LLVMMul)) {
                    LLVMReplaceAllUsesWith(ins_2, ins_1);
                    replacement_has_happened = true; // we have replacement_has_happened in each if statement content b/c if we have the case where the operands the the same in opposite order but shared_type_of_ins is substraction then we cannot substitute 
                }
                // we handle substraction separately b/c substraction is not commutative so it requires the same order
                if (operands_are_the_same_in_order && shared_type_of_ins == LLVMSub){
                    LLVMReplaceAllUsesWith(ins_2, ins_1);
                    replacement_has_happened =true;
                }
            }

            // we separate these conditionals for readability

            if ((type_of_ins_1 == LLVMLoad && LLVMGetInstructionOpcode(ins_2) == LLVMLoad) && (LLVMGetOperand(ins_1, 0) == LLVMGetOperand(ins_2, 0))){
                if (!is_store_in_between_shared_memory_uses(ins_1, ins_2)){
                    LLVMReplaceAllUsesWith(ins_2, ins_1);
                    replacement_has_happened = true;
                }
            }

            ins_2 = ins_2_next;
        }
    }
    return replacement_has_happened;
}

bool is_store_in_between_shared_memory_uses(LLVMValueRef first_instruction, LLVMValueRef second_instruction) {
    
    // we get the shared pointer to the memory address
    LLVMValueRef memory_ptr = LLVMGetOperand(first_instruction, 0);

    for (LLVMValueRef instruction = LLVMGetNextInstruction(first_instruction); 
        instruction != NULL && instruction != second_instruction; 
        instruction = LLVMGetNextInstruction(instruction)) {
            LLVMOpcode opcode = LLVMGetInstructionOpcode(instruction);
            if (opcode == LLVMStore && memory_ptr == LLVMGetOperand(instruction, 1)) {
                return true; // meaning that there is an store operation with the same operand in between
            }
    }
    return false;
}

bool run_constant_folding(LLVMBasicBlockRef bb){
    bool changed = false; // to indicate if constant folding has been performed

    LLVMValueRef instruction = LLVMGetFirstInstruction(bb);
    LLVMOpcode type_of_ins;
    while (instruction != NULL){
        type_of_ins = LLVMGetInstructionOpcode(instruction);
        LLVMValueRef next = LLVMGetNextInstruction(instruction); // to continue iterating later
        if (type_of_ins == LLVMAdd || type_of_ins == LLVMSub || type_of_ins == LLVMMul){
            
            LLVMValueRef first_operand = LLVMGetOperand(instruction, 0);
            LLVMBool is_first_operand_cons = LLVMIsConstant(first_operand);
            LLVMValueRef second_operand = LLVMGetOperand(instruction, 1);
            LLVMBool is_second_operand_cons = LLVMIsConstant(second_operand);

            LLVMValueRef folded_result = NULL;

            
            if (is_first_operand_cons && is_second_operand_cons){
                if (type_of_ins == LLVMAdd){
                    folded_result = LLVMConstAdd(first_operand, second_operand);
                }

                if (type_of_ins == LLVMSub){
                    folded_result = LLVMConstSub(first_operand, second_operand);
                }

                if (type_of_ins == LLVMMul){
                    folded_result = LLVMConstMul(first_operand, second_operand);
                }
            }

            if (folded_result != NULL){
                LLVMReplaceAllUsesWith(instruction, folded_result);
                LLVMInstructionEraseFromParent(instruction);
                changed = true;
            }
            
        }
        instruction = next;
    }
    return changed;
}

bool instruction_should_be_kept(LLVMValueRef instruction){
    LLVMOpcode ins_type = LLVMGetInstructionOpcode(instruction);
    // if we have any of the following cases then they are relevant in control flow and memory allocation
    // thus removing them would be dangerous for the successful execution of the program
    if (LLVMIsATerminatorInst(instruction) != NULL || ins_type == LLVMStore || ins_type == LLVMCall) {
        return true;
    }

    return false;
}


bool run_dead_code_elimination(LLVMValueRef func){
    // has_changed useful to get to the fixed point state. If we have reached a 
    // cycle on which there is no change then all dead code elimination has been performed
    bool has_changed_this_cycle = true;  // we initialize to true just to start the loop
    bool has_changed_at_all = false;

    while (has_changed_this_cycle){

        has_changed_this_cycle = false;

        for (LLVMBasicBlockRef bb = LLVMGetFirstBasicBlock(func); bb != NULL; bb = LLVMGetNextBasicBlock(bb)) {

            for (LLVMValueRef inst = LLVMGetFirstInstruction(bb); inst != NULL; ) {
                LLVMValueRef next = LLVMGetNextInstruction(inst);
                
                bool is_unused = (LLVMGetFirstUse(inst) == NULL);

                if (is_unused && !instruction_should_be_kept(inst)) {

                    LLVMInstructionEraseFromParent(inst);

                    has_changed_this_cycle = true;
                    has_changed_at_all = true;
                }

                inst = next;
            }
        }
    }
    return has_changed_at_all;
}

// computing the set GEN[B] for a basic block B
std::unordered_set <LLVMValueRef> compute_gen_set_for_block(LLVMBasicBlockRef bb) {
    std::unordered_set <LLVMValueRef> block_gen_set = {};
    // we go over each instruction in the basic block
    for (LLVMValueRef ins = LLVMGetFirstInstruction(bb); ins != NULL; ins = LLVMGetNextInstruction(ins)) {
        LLVMOpcode type_of_ins = LLVMGetInstructionOpcode(ins);
        // if a instruction of type store is found then it is inserted
        if (type_of_ins == LLVMStore) {
            block_gen_set.insert(ins);
            LLVMValueRef ptr = LLVMGetOperand(ins, 1);
            LLVMValueRef ins_to_eliminate = NULL;
            // if any other instruction that references to the same ptr was already in place it is erased
            // one at a time
            for (LLVMValueRef element : block_gen_set) {
                if (ptr == LLVMGetOperand(element, 1) && element != ins) {
                    ins_to_eliminate = element;
                    break;
                }
            }

            if (ins_to_eliminate != NULL){
                block_gen_set.erase(ins_to_eliminate);
            }
        }
    }
    return block_gen_set;
} 

// computing the set of all store instructions in the function
std::unordered_set <LLVMValueRef> set_of_all_store (LLVMValueRef func) {
    std::unordered_set <LLVMValueRef> set_of_all_store = {};
    for (LLVMBasicBlockRef bb = LLVMGetFirstBasicBlock(func); bb != NULL; bb = LLVMGetNextBasicBlock(bb)){
        for (LLVMValueRef ins = LLVMGetFirstInstruction(bb); ins != NULL; ins = LLVMGetNextInstruction(ins)){
            LLVMOpcode type_of_ins = LLVMGetInstructionOpcode(ins);
            if (type_of_ins == LLVMStore) {
                set_of_all_store.insert(ins);
            }
        }
    }
}

// computing the set KILL[B] for a basic block B
std::unordered_set <LLVMValueRef> compute_kill_set_for_block(LLVMBasicBlockRef bb) {

    std::unordered_set <LLVMValueRef> block_kill_set = {};

    // getting the function to determine the set of all stores
    LLVMValueRef func = LLVMGetBasicBlockParent(bb);
    std::unordered_set <LLVMValueRef> set_of_stores = set_of_all_store(func);

    for (LLVMValueRef ins = LLVMGetFirstInstruction(bb); ins != NULL; ins = LLVMGetNextInstruction(ins)){
        if (LLVMGetInstructionOpcode(ins) == LLVMStore){
            for (LLVMValueRef store_ins : set_of_stores) {
                if (store_ins != ins) { // so that all the others are added
                    block_kill_set.insert(store_ins);
                }
            }
        }
    }
}

// Getting the predecessors map where the keys are the blocks and the values are their corresponding predecessors
std::unordered_map <LLVMBasicBlockRef, std::unordered_set <LLVMBasicBlockRef>> compute_predecesor_blocks (LLVMValueRef func) {
    std::unordered_map <LLVMBasicBlockRef, std::unordered_set <LLVMBasicBlockRef>> predecessors_map;

    for (LLVMBasicBlockRef bb = LLVMGetFirstBasicBlock(func); bb != NULL; bb = LLVMGetNextBasicBlock(bb)) {
        LLVMValueRef terminator = LLVMGetBasicBlockTerminator(bb); // getting the terminator to access the successors
        if (terminator == NULL) {
            continue;
        }
        unsigned successor_index = 0;
        while (successor_index < LLVMGetNumSuccessors(terminator)) {
            LLVMBasicBlockRef successor = LLVMGetSuccessor(terminator, successor_index);
            predecessors_map[successor].insert(bb); // because the successor's predecessor is the current block
            successor_index++;
        }
    }
    return predecessors_map;
}

std::unordered_map <LLVMBasicBlockRef, IN_and_OUT> in_and_out_sets_map(LLVMvalueRef func) {
    // we begin by computing the predecessors for each block for easier later computation
    std::unordered_map <LLVMBasicBlockRef, std::unordered_set <LLVMBasicBlockRef>> predecessors_map = compute_predecesor_blocks(func);
    // initializing each "in set" as empty and also initializing each "out set" as the gen set
    std::unordered_map <LLVMBasicBlockRef, IN_and_OUT> in_and_out_sets_map;
    for (LLVMBasicBlockRef bb = LLVMGetFirstBasicBlock(func);
        bb != NULL;
        bb = LLVMGetNextBasicBlock(bb)) {
            std::unordered_set <LLVMValueRef> in_set = {};
            std::unordered_set <LLVMValueRef> out_set = compute_gen_set_for_block(bb); 

            IN_and_OUT IN_and_OUT_element;
            // we provide the in_set and out_set data to the IN_and_OUT_element
            IN_and_OUT_element.in_set_in_block = in_set;
            IN_and_OUT_element.out_set_in_block = out_set;

            in_and_out_sets_map[bb] = IN_and_OUT_element;
        } 

    bool change = true; // in order to stop when we have reached a fixed point
    while (change) {
        change = false; // if a change is found this will change to true again
        for (LLVMBasicBlockRef bb = LLVMGetFirstBasicBlock(func);
            bb != NULL;
            bb = LLVMGetNextBasicBlock(bb)) {
                std::unordered_set <LLVMBasicBlockRef> predecessors_of_bb = predecessors_map[bb];
                // computing and storing IN[B] as the union of the predecessors OUT
                for (LLVMBasicBlockRef predecessor : predecessors_of_bb) {
                    in_and_out_sets_map[bb].in_set_in_block.insert(in_and_out_sets_map[predecessor].out_set_in_block.begin(), in_and_out_sets_map[predecessor].out_set_in_block.end());
                }
                // Storing the old OUT of the block to compare with the new one and see if change has ocurred
                std::unordered_set <LLVMValueRef> old_out = in_and_out_sets_map[bb].out_set_in_block;
                // we compute the gen set of the block to do OUT[B] = GEN[B] union (in[B] - kill[B])
                std::unordered_set <LLVMValueRef> gen_set_of_block = compute_gen_set_for_block(bb);
                // first we include all the gen set elements associated
                in_and_out_sets_map[bb].out_set_in_block.insert(gen_set_of_block.begin(), gen_set_of_block.end());
                // inserting IN[B] - KILL[B] to finish defining OUT[B]
                std::unordered_set <LLVMValueRef> in_instructions = in_and_out_sets_map[bb].in_set_in_block;
                for (LLVMValueRef IN_instruction : in_instructions) {
                    std::unordered_set <LLVMValueRef> kill_instructions_for_block = compute_kill_set_for_block(bb);
                    for (LLVMValueRef KILL_instruction : kill_instructions_for_block) {
                        if (IN_instruction != KILL_instruction) {
                            in_and_out_sets_map[bb].out_set_in_block.insert(IN_instruction);
                        }
                    }
                }
                // checking if a change has occured
                if (in_and_out_sets_map[bb].out_set_in_block != old_out) {
                    change = true;
                }
            }
    }
}

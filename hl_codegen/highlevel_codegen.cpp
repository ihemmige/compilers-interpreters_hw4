// Copyright (c) 2021-2024, David H. Hovemeyer <david.hovemeyer@gmail.com>
//
// Permission is hereby granted, free of charge, to any person obtaining a
// copy of this software and associated documentation files (the "Software"),
// to deal in the Software without restriction, including without limitation
// the rights to use, copy, modify, merge, publish, distribute, sublicense,
// and/or sell copies of the Software, and to permit persons to whom the
// Software is furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included
// in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
// THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR
// OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
// ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
// OTHER DEALINGS IN THE SOFTWARE.

#include <cassert>
#include "node.h"
#include "instruction.h"
#include "highlevel.h"
#include "ast.h"
#include "parse.tab.h"
#include "grammar_symbols.h"
#include "exceptions.h"
#include "local_storage_allocation.h"
#include "highlevel_codegen.h"

#include <iostream> 
using namespace std;

// Adjust an opcode for a basic type
HighLevelOpcode get_opcode(HighLevelOpcode base_opcode, std::shared_ptr<Type> type) {
  if (type->is_basic())
    return static_cast<HighLevelOpcode>(int(base_opcode) + int(type->get_basic_type_kind()));
  else if (type->is_pointer())
    return static_cast<HighLevelOpcode>(int(base_opcode) + int(BasicTypeKind::LONG));
  else
    RuntimeError::raise("attempt to use type '%s' as data in opcode selection", type->as_str().c_str());
}

HighLevelOpcode generate_bin_opcode(std::string& oper, Node *n) {
  if (oper == "+") {
    return get_opcode(HINS_add_b, n->get_type());
  } else if (oper == ">=") {
    return get_opcode(HINS_cmpgte_b, n->get_type());
  } else if (oper == "<") {
    return get_opcode(HINS_cmplt_b, n->get_type());
  } else if (oper == "!=") {
    return get_opcode(HINS_cmpneq_b, n->get_type());
  } else if (oper == "/") {
    return get_opcode(HINS_div_b, n->get_type());
  }  else if (oper == "==") {
    return get_opcode(HINS_cmpeq_b, n->get_type());
  } else if (oper == "*") {
    return get_opcode(HINS_mul_b, n->get_type());
  } else if (oper == "<=") {
    return get_opcode(HINS_cmplte_b, n->get_type());
  } else if (oper == "%") {
    return get_opcode(HINS_mod_b, n->get_type());
  } else if (oper == ">") {
    return get_opcode(HINS_cmpgt_b, n->get_type());
  } else if (oper == "-") {
    return get_opcode(HINS_sub_b, n->get_type());
  }
}

HighLevelCodegen::HighLevelCodegen(const Options &options, int next_label_num)
  : m_options(options)
  , m_next_label_num(next_label_num)
{
}

HighLevelCodegen::~HighLevelCodegen() {
}

void HighLevelCodegen::generate(std::shared_ptr<Function> function) {
  assert(function->get_funcdef_ast() != nullptr);
  assert(!function->get_hl_iseq());

  // Create empty InstructionSequence to hold high-level instructions
  std::shared_ptr<InstructionSequence> hl_iseq(new InstructionSequence());
  function->set_hl_iseq(hl_iseq);

  // Member functions can use m_function to access the Function object
  m_function = function;

  // Visit function definition
  visit(function->get_funcdef_ast());
}

void HighLevelCodegen::visit_function_definition(Node *n) {
  // generate the name of the label that return instructions should target
  std::string fn_name = n->get_kid(1)->get_str();
  m_return_label_name = ".L" + fn_name + "_return";

  unsigned total_local_storage = 0U;

  total_local_storage = n->get_total_local_storage();

  get_hl_iseq()->append(new Instruction(HINS_enter, Operand(Operand::IMM_IVAL, total_local_storage)));

  // move each argument into its local register
  Node* args = n->get_kid(2);
  for (auto iter = args->cbegin(); iter != args->cend(); iter++) {
    Node* arg = *iter;

    // source register
    Operand source = Operand(Operand::VREG, std::distance(args->cbegin(), iter) + 1);
    
    // function param virtual register
    Operand dest = Operand(Operand::VREG, arg->get_symbol()->get_vreg());

    // move type
    std::shared_ptr<Type> param_type = arg->get_type();
    if (param_type->is_array()){
      param_type = param_type->get_base_type();
    }
    HighLevelOpcode opcode = get_opcode(HINS_mov_b, param_type);

    get_hl_iseq()->append(new Instruction(opcode, dest, source));
  }

  // visit body
  visit(n->get_kid(3));

  get_hl_iseq()->define_label(m_return_label_name);
  get_hl_iseq()->append(new Instruction(HINS_leave, Operand(Operand::IMM_IVAL, total_local_storage)));
  get_hl_iseq()->append(new Instruction(HINS_ret));
}

void HighLevelCodegen::visit_statement_list(Node *n) {
  // TODO: implement
  for (auto iter = n->cbegin(); iter != n->cend(); iter++) {
    visit(*iter);
  }
}

void HighLevelCodegen::visit_expression_statement(Node *n) {
  // TODO: implement
  visit(n->get_kid(0));
}

void HighLevelCodegen::visit_return_statement(Node *n) {
  // TODO: anything else here?
  get_hl_iseq()->append(new Instruction(HINS_jmp, Operand(Operand::LABEL, m_return_label_name)));
}

void HighLevelCodegen::visit_return_expression_statement(Node *n) {
  // A possible implementation:
  Node *expr = n->get_kid(0);

  // generate code to evaluate the expression
  visit(expr);

  // move the computed value to the return value vreg
  HighLevelOpcode mov_opcode = get_opcode(HINS_mov_b, expr->get_type());
  if (expr->get_symbol() && expr->get_symbol()->get_align() != -1) { // if the value is in local storage, dereference the MEM location
    get_hl_iseq()->append(new Instruction(mov_opcode, Operand(Operand::VREG, LocalStorageAllocation::VREG_RETVAL), Operand(Operand::VREG_MEM, expr->get_operand().get_base_reg())));
  } else { // otherwise just the register is fine
    get_hl_iseq()->append(new Instruction(mov_opcode, Operand(Operand::VREG, LocalStorageAllocation::VREG_RETVAL), expr->get_operand()));
  }

  // jump to the return label
  visit_return_statement(n);
}

void HighLevelCodegen::visit_while_statement(Node *n) {
  std::string body_label = next_label();
  std::string check_label = next_label();
  get_hl_iseq()->append(new Instruction(HINS_jmp, Operand(Operand::LABEL, check_label)));

  // loop body
  get_hl_iseq()->define_label(body_label);
  visit(n->get_kid(1));

  // loop condition
  get_hl_iseq()->define_label(check_label);
  visit(n->get_kid(0));
  get_hl_iseq()->append(new Instruction(HINS_cjmp_t, n->get_kid(0)->get_operand(), Operand(Operand::LABEL, body_label)));
}

void HighLevelCodegen::visit_do_while_statement(Node *n) {
  std::string body_label = next_label();
  get_hl_iseq()->define_label(body_label);

  // loop body
  visit(n->get_kid(0));
  
  // condition
  visit(n->get_kid(1));
  get_hl_iseq()->append(new Instruction(HINS_cjmp_t, n->get_kid(1)->get_operand(), Operand(Operand::LABEL, body_label))); // jump back up
}

void HighLevelCodegen::visit_for_statement(Node *n) {
  std::string body_label = next_label();
  std::string check_label = next_label();

  // initialization
  visit(n->get_kid(0));
  get_hl_iseq()->append(new Instruction(HINS_jmp, Operand(Operand::LABEL, check_label)));

  // loop body
  get_hl_iseq()->define_label(body_label);
  visit(n->get_kid(3));

  // increment
  visit(n->get_kid(2));

  // conditiion
  get_hl_iseq()->define_label(check_label);
  visit(n->get_kid(1));
  get_hl_iseq()->append(new Instruction(HINS_cjmp_t, n->get_kid(1)->get_operand(), Operand(Operand::LABEL, body_label)));
}

void HighLevelCodegen::visit_if_statement(Node *n) {
  // condition
  visit(n->get_kid(0));

  // skip body if false
  std::string skip_if = next_label();
  get_hl_iseq()->append(new Instruction(HINS_cjmp_f, n->get_kid(0)->get_operand(), Operand(Operand::LABEL, skip_if)));

  // body
  visit(n->get_kid(1));

  // skip label comes after body
  get_hl_iseq()->define_label(skip_if);
}

void HighLevelCodegen::visit_if_else_statement(Node *n) {
  std::string post_statement = next_label();
  std::string else_label = next_label();

  // condition
  visit(n->get_kid(0));
  get_hl_iseq()->append(new Instruction(HINS_cjmp_f, n->get_kid(0)->get_operand(), Operand(Operand::LABEL, else_label))); // jump if false

  // if body
  visit(n->get_kid(1));
  get_hl_iseq()->append(new Instruction(HINS_jmp, Operand(Operand::LABEL, post_statement)));

  // else label and body
  get_hl_iseq()->define_label(else_label);
  visit(n->get_kid(2));

  // after the if-else
  get_hl_iseq()->define_label(post_statement);
}

void HighLevelCodegen::visit_binary_expression(Node *n) {
  // TODO: implement
  Node* lhs = n->get_kid(1);
  Node* rhs = n->get_kid(2);
  
  // create high level instruction based on operation type
  std::string oper = n->get_kid(0)->get_str();
  if (oper == "=") {
    visit(rhs);
    visit(lhs);
    get_hl_iseq()->append(new Instruction(get_opcode(HINS_mov_b, n->get_type()), lhs->get_operand(), rhs->get_operand()));
    n->set_operand(lhs->get_operand());
  } else {
    HighLevelOpcode opcode = generate_bin_opcode(oper, n);
    visit(lhs);
    visit(rhs);

    // move memrefs to a temp register
    Operand lhs_oper = lhs->get_operand();
    if (lhs_oper.get_kind() == Operand::VREG_MEM) {
      Operand temp(Operand::VREG, m_function->get_vreg_alloc()->alloc_local());
      get_hl_iseq()->append(new Instruction(get_opcode(HINS_mov_b, n->get_type()), temp, lhs->get_operand()));
      lhs_oper = temp;
    }
    Operand rhs_oper = rhs->get_operand();
    if (rhs_oper.get_kind() == Operand::VREG_MEM) {
      Operand temp(Operand::VREG, m_function->get_vreg_alloc()->alloc_local());
      get_hl_iseq()->append(new Instruction(get_opcode(HINS_mov_b, n->get_type()), temp, rhs->get_operand()));
      rhs_oper = temp;
    }
    
    Operand dest(Operand::VREG, m_function->get_vreg_alloc()->alloc_local());
    get_hl_iseq()->append(new Instruction(opcode, dest, lhs_oper, rhs_oper));
    n->set_operand(dest);
  }
}

void HighLevelCodegen::visit_unary_expression(Node *n) {
  // TODO: implement
  Node* oper = n->get_kid(0);
  int oper_tag = oper->get_tag();
  Node* value = n->get_kid(1);
  switch(oper_tag) {
    case TOK_AMPERSAND: {
      visit(value);
      n->set_operand(value->get_operand());
      return;
    }
    case TOK_ASTERISK: {
      visit(value);
      Operand temp(Operand::VREG_MEM, value->get_operand().get_base_reg());
      n->set_operand(temp);
    }
  }  
}

void HighLevelCodegen::visit_function_call_expression(Node *n) {
  // TODO: implement
  std::string func_name = n->get_kid(0)->get_kid(0)->get_str();
  Node* args = n->get_kid(1);
  for (auto iter = args->cbegin(); iter != args->cend(); iter++) {
    Node* arg = *iter;
    visit(arg);

    // move params into virtual registers for function
    // source register
    Operand source = arg->get_operand();

    // function param virtual register
    Operand dest = Operand(Operand::VREG, std::distance(args->cbegin(), iter) + 1);

    // move type
    std::shared_ptr<Type> param_type = arg->get_type();
    if (param_type->is_array()){
      param_type = std::make_shared<PointerType>(param_type->get_base_type());
    }

    HighLevelOpcode opcode = get_opcode(HINS_mov_b, param_type);
    get_hl_iseq()->append(new Instruction(opcode, dest, source));
  }

  // call function
  get_hl_iseq()->append(new Instruction(HINS_call, Operand(Operand::LABEL, func_name)));

  // return value is in vr0; move to local register
  Operand dest(Operand::VREG, m_function->get_vreg_alloc()->alloc_local());
  get_hl_iseq()->append(new Instruction(get_opcode(HINS_mov_b, n->get_type()), dest, Operand(Operand::VREG, 0)));
  n->set_operand(dest);
}

void HighLevelCodegen::visit_field_ref_expression(Node *n) {
  // visit struct variable
  Node* struct_var = n->get_kid(0);
  visit(struct_var);
  Symbol* struct_symbol = struct_var->get_symbol();

  // determine offset of field in struct; store in vreg
  Node* field = n->get_kid(1);
  std::string field_name = field->get_str();
  int field_offset = struct_symbol->get_type()->get_field_offset(field_name);
  int offset_reg = m_function->get_vreg_alloc()->alloc_local();
  get_hl_iseq()->append(new Instruction(HINS_mov_q, Operand(Operand::VREG, offset_reg), Operand(Operand::IMM_IVAL, field_offset)));

  // generate the field's address
  int field_reg = m_function->get_vreg_alloc()->alloc_local();
  get_hl_iseq()->append(new Instruction(HINS_add_q, Operand(Operand::VREG, field_reg), struct_var->get_operand(), Operand(Operand::VREG, offset_reg)));
  n->set_operand(Operand(Operand::VREG_MEM, field_reg));
}

void HighLevelCodegen::visit_indirect_field_ref_expression(Node *n) {
  // visit struct variable
  Node* struct_var = n->get_kid(0);
  visit(struct_var);
  Symbol* struct_symbol = struct_var->get_symbol();

  // determine offset of field in struct; store in vreg
  Node* field = n->get_kid(1);
  std::string field_name = field->get_str();
  int field_offset = struct_symbol->get_type()->get_base_type()->get_field_offset(field_name);
  int offset_reg = m_function->get_vreg_alloc()->alloc_local();
  get_hl_iseq()->append(new Instruction(HINS_mov_q, Operand(Operand::VREG, offset_reg), Operand(Operand::IMM_IVAL, field_offset)));

  // generate the field's address
  int field_reg = m_function->get_vreg_alloc()->alloc_local();
  get_hl_iseq()->append(new Instruction(HINS_add_q, Operand(Operand::VREG, field_reg), struct_var->get_operand(), Operand(Operand::VREG, offset_reg)));
  n->set_operand(Operand(Operand::VREG_MEM, field_reg));
}

void HighLevelCodegen::visit_array_element_ref_expression(Node *n) {
  // visit array var
  Node* array_var = n->get_kid(0);
  visit(array_var);
  int elem_size = n->get_kid(0)->get_symbol()->get_type()->get_base_type()->get_storage_size();

  // process index
  visit(n->get_kid(1));
  int index_vreg = m_function->get_vreg_alloc()->alloc_local();
  get_hl_iseq()->append(new Instruction(HINS_sconv_lq, Operand(Operand::VREG, index_vreg), n->get_kid(1)->get_operand()));
  
  // generate offset
  int offset_vreg = m_function->get_vreg_alloc()->alloc_local();
  get_hl_iseq()->append(new Instruction(HINS_mul_q, Operand(Operand::VREG, offset_vreg), Operand(Operand::VREG, index_vreg), Operand(Operand::IMM_IVAL, elem_size)));

  // get desired element (start + offset)
  int target_vreg = m_function->get_vreg_alloc()->alloc_local();
  get_hl_iseq()->append(new Instruction(HINS_add_q, Operand(Operand::VREG, target_vreg), array_var->get_operand(), Operand(Operand::VREG, offset_vreg)));

  // dereference pointer and store value
  // int element_vreg = m_function->get_vreg_alloc()->alloc_local();
  // HighLevelOpcode mov_opcode = get_opcode(HINS_mov_b, n->get_type());
  // get_hl_iseq()->append(new Instruction(mov_opcode, Operand(Operand::VREG, element_vreg), Operand(Operand::VREG_MEM, target_vreg)));

  n->set_operand(Operand(Operand::VREG_MEM, target_vreg));
}

void HighLevelCodegen::visit_variable_ref(Node *n) {
  Symbol* var = n->get_symbol();
  assert(var->get_vreg() != -1 || var->get_align() != -1);
  if (var->get_vreg() != -1) {
    n->set_operand(Operand(Operand::VREG, var->get_vreg()));
  } else if (var->get_align() != -1) {
    int vreg = m_function->get_vreg_alloc()->alloc_local();
    get_hl_iseq()->append(new Instruction(HINS_localaddr, Operand(Operand::VREG, vreg), Operand(Operand::IMM_IVAL, var->get_align())));
    n->set_operand(Operand(Operand::VREG, vreg));
  }
}

void HighLevelCodegen::visit_literal_value(Node *n) {
  // A partial implementation (note that this won't work correctly
  // for string constants!):
  /*
  LiteralValue val = n->get_literal_value();
  int vreg = next_temp_vreg();
  Operand dest(Operand::VREG, vreg);
  HighLevelOpcode mov_opcode = get_opcode(HINS_mov_b, n->get_type());
  get_hl_iseq()->append(new Instruction(mov_opcode, dest, Operand(Operand::IMM_IVAL, val.get_int_value())));
  n->set_operand(dest);
  */
  LiteralValue val(std::stoi(n->get_kid(0)->get_str()), false, false);
  Operand dest(Operand::VREG, m_function->get_vreg_alloc()->alloc_local());
  HighLevelOpcode mov_opcode = get_opcode(HINS_mov_b, n->get_type());
  get_hl_iseq()->append(new Instruction(mov_opcode, dest, Operand(Operand::IMM_IVAL, val.get_int_value())));
  n->set_operand(dest);
  // TODO: SUPPORT FOR STRING CONSTANTS (CHARS)
}

void HighLevelCodegen::visit_implicit_conversion(Node *n) {
  // TODO: implement
}

std::string HighLevelCodegen::next_label() {
  std::string label = ".L" + std::to_string(m_next_label_num++);
  return label;
}

// TODO: additional private member functions

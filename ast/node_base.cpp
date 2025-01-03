// Copyright (c) 2021-2023, David H. Hovemeyer <david.hovemeyer@gmail.com>
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
#include "node_base.h"

NodeBase::NodeBase()
{
  m_type = nullptr;
  m_symbol = nullptr;
  this->literal = false;
}

NodeBase::~NodeBase() {
}

void NodeBase::set_symbol(Symbol *symbol) {
  assert(!has_symbol());
  assert(m_type == nullptr);
  m_symbol = symbol;
}

void NodeBase::set_type(const std::shared_ptr<Type> &type) {
  assert(!has_symbol());
  assert(!m_type);
  m_type = type;
}

bool NodeBase::has_symbol() const {
  return m_symbol != nullptr;
}

Symbol *NodeBase::get_symbol() const {
  return m_symbol;
}

std::shared_ptr<Type> NodeBase::get_type() const {
  // this shouldn't be called unless there is actually a type
  // associated with this node

  if (has_symbol())
    return m_symbol->get_type(); // Symbol will definitely have a valid Type
  else {
    assert(m_type); // make sure a Type object actually exists
    return m_type;
  }
}

void NodeBase::override_type(const std::shared_ptr<Type> &type) {
  assert(m_type);
  m_type = type;
}

void NodeBase::make_literal() {
  this->literal = true;
};

bool NodeBase::is_literal() {
  return this->literal;
}

void NodeBase::set_total_local_storage(unsigned size) {
  m_total_local_storage = size;
}

unsigned NodeBase::get_total_local_storage() {
  return m_total_local_storage;
}

void NodeBase::set_str_lit_name(std::string value) {
  str_lit_name = value;
}

std::string NodeBase::get_str_lit_name() {
  return str_lit_name;
}
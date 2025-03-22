/******************************************
Copyright (C) 2023 Authors of GANAK, see AUTHORS file

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
***********************************************/

#include "comp.hpp"
/* #include "common.hpp" */
#include "counter.hpp"

using namespace GanakInt;

Comp* GanakInt::copy_comp(const Comp* other, const Counter* counter) {
  Comp* ptr = reserve_comp_space(other->nVars(), other->num_long_cls());
  const uint32_t* p = other->vs_cls_data();
  while(*p != sentinel) {
    if (counter->is_unknown(*p))  ptr->add_var(*p);
    p++;
  }
  ptr->close_vars_data();
  p++;
  while(*p != sentinel) {
    ptr->add_cl(*p);
    p++;
  }
  ptr->close_cls_data();
  ptr->set_num_bin_cls(other->num_bin_cls());
  ptr->set_trail_sz(counter->get_trail_size());
  /* memcpy(ptr, other, sizeof(Comp) + other->get_size()*sizeof(uint32_t)); */
  return ptr;
}


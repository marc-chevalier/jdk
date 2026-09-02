/*
 * Copyright (c) 1997, 2026, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 *
 */

#include "memory/allocation.inline.hpp"
#include "opto/addnode.hpp"
#include "opto/castnode.hpp"
#include "opto/cfgnode.hpp"
#include "opto/connode.hpp"
#include "opto/loopnode.hpp"
#include "opto/machnode.hpp"
#include "opto/movenode.hpp"
#include "opto/mulnode.hpp"
#include "opto/phaseX.hpp"
#include "opto/rangeinference.hpp"
#include "opto/subnode.hpp"
#include "runtime/stubRoutines.hpp"

// Portions of code courtesy of Clifford Click

// Classic Add functionality.  This covers all the usual 'add' behaviors for
// an algebraic ring.  Add-integer, add-float, add-double, and binary-or are
// all inherited from this class.  The various identity values are supplied
// by virtual functions.


//=============================================================================
//------------------------------hash-------------------------------------------
// Hash function over AddNodes.  Needs to be commutative; i.e., I swap
// (commute) inputs to AddNodes willy-nilly so the hash function must return
// the same value in the presence of edge swapping.
uint AddNode::hash() const {
  return (uintptr_t)in(1) + (uintptr_t)in(2) + Opcode();
}

//------------------------------Identity---------------------------------------
// If either input is a constant 0, return the other input.
Node* AddNode::Identity(PhaseGVN* phase) {
  const Type *zero = add_id();  // The additive identity
  if( phase->type( in(1) )->higher_equal( zero ) ) return in(2);
  if( phase->type( in(2) )->higher_equal( zero ) ) return in(1);
  return this;
}

//------------------------------commute----------------------------------------
// Commute operands to move loads and constants to the right.
static bool commute(PhaseGVN* phase, Node* add) {
  Node *in1 = add->in(1);
  Node *in2 = add->in(2);

  // convert "max(a,b) + min(a,b)" into "a+b".
  if ((in1->Opcode() == add->as_Add()->max_opcode() && in2->Opcode() == add->as_Add()->min_opcode())
      || (in1->Opcode() == add->as_Add()->min_opcode() && in2->Opcode() == add->as_Add()->max_opcode())) {
    Node *in11 = in1->in(1);
    Node *in12 = in1->in(2);

    Node *in21 = in2->in(1);
    Node *in22 = in2->in(2);

    if ((in11 == in21 && in12 == in22) ||
        (in11 == in22 && in12 == in21)) {
      add->set_req_X(1, in11, phase);
      add->set_req_X(2, in12, phase);
      return true;
    }
  }

  bool con_left = phase->type(in1)->singleton();
  bool con_right = phase->type(in2)->singleton();

  // Convert "1+x" into "x+1".
  // Right is a constant; leave it
  if( con_right ) return false;
  // Left is a constant; move it right.
  if( con_left ) {
    add->swap_edges(1, 2);
    return true;
  }

  // Convert "Load+x" into "x+Load".
  // Now check for loads
  if (in2->is_Load()) {
    if (!in1->is_Load()) {
      // already x+Load to return
      return false;
    }
    // both are loads, so fall through to sort inputs by idx
  } else if( in1->is_Load() ) {
    // Left is a Load and Right is not; move it right.
    add->swap_edges(1, 2);
    return true;
  }

  PhiNode *phi;
  // Check for tight loop increments: Loop-phi of Add of loop-phi
  if (in1->is_Phi() && (phi = in1->as_Phi()) && phi->region()->is_Loop() && phi->in(2) == add)
    return false;
  if (in2->is_Phi() && (phi = in2->as_Phi()) && phi->region()->is_Loop() && phi->in(2) == add) {
    add->swap_edges(1, 2);
    return true;
  }

  // Otherwise, sort inputs (commutativity) to help value numbering.
  if( in1->_idx > in2->_idx ) {
    add->swap_edges(1, 2);
    return true;
  }
  return false;
}

//------------------------------Idealize---------------------------------------
// If we get here, we assume we are associative!
Node *AddNode::Ideal(PhaseGVN *phase, bool can_reshape) {
  const Type *t1 = phase->type(in(1));
  const Type *t2 = phase->type(in(2));
  bool con_left  = t1->singleton();
  bool con_right = t2->singleton();

  // Check for commutative operation desired
  if (commute(phase, this)) return this;

  AddNode *progress = nullptr;             // Progress flag

  // Convert "(x+1)+2" into "x+(1+2)".  If the right input is a
  // constant, and the left input is an add of a constant, flatten the
  // expression tree.
  Node *add1 = in(1);
  Node *add2 = in(2);
  int add1_op = add1->Opcode();
  int this_op = Opcode();
  if (con_right && t2 != Type::TOP && // Right input is a constant?
      add1_op == this_op) { // Left input is an Add?

    // Type of left _in right input
    const Type *t12 = phase->type(add1->in(2));
    if (t12->singleton() && t12 != Type::TOP) { // Left input is an add of a constant?
      // Check for rare case of closed data cycle which can happen inside
      // unreachable loops. In these cases the computation is undefined.
#ifdef ASSERT
      Node *add11    = add1->in(1);
      int   add11_op = add11->Opcode();
      if ((add1 == add1->in(1))
          || (add11_op == this_op && add11->in(1) == add1)) {
        assert(false, "dead loop in AddNode::Ideal");
      }
#endif
      // The Add of the flattened expression
      Node *x1 = add1->in(1);
      Node *x2 = phase->makecon(add1->as_Add()->add_ring(t2, t12));
      set_req_X(2, x2, phase);
      set_req_X(1, x1, phase);
      progress = this;            // Made progress
      add1 = in(1);
      add1_op = add1->Opcode();
    }
  }

  // Convert "(x+1)+y" into "(x+y)+1".  Push constants down the expression tree.
  if (add1_op == this_op && !con_right) {
    Node *a12 = add1->in(2);
    const Type *t12 = phase->type( a12 );
    if (t12->singleton() && t12 != Type::TOP && (add1 != add1->in(1)) &&
        !(add1->in(1)->is_Phi() && (add1->in(1)->as_Phi()->is_tripcount(T_INT) || add1->in(1)->as_Phi()->is_tripcount(T_LONG)))) {
      assert(add1->in(1) != this, "dead loop in AddNode::Ideal");
      add2 = add1->clone();
      add2->set_req(2, in(2));
      add2 = phase->transform(add2);
      set_req_X(1, add2, phase);
      set_req_X(2, a12, phase);
      progress = this;
      add2 = a12;
    }
  }

  // Convert "x+(y+1)" into "(x+y)+1".  Push constants down the expression tree.
  int add2_op = add2->Opcode();
  if (add2_op == this_op && !con_left) {
    Node *a22 = add2->in(2);
    const Type *t22 = phase->type( a22 );
    if (t22->singleton() && t22 != Type::TOP && (add2 != add2->in(1)) &&
        !(add2->in(1)->is_Phi() && (add2->in(1)->as_Phi()->is_tripcount(T_INT) || add2->in(1)->as_Phi()->is_tripcount(T_LONG)))) {
      assert(add2->in(1) != this, "dead loop in AddNode::Ideal");
      Node *addx = add2->clone();
      addx->set_req(1, in(1));
      addx->set_req(2, add2->in(1));
      addx = phase->transform(addx);
      set_req_X(1, addx, phase);
      set_req_X(2, a22, phase);
      progress = this;
    }
  }

  return progress;
}

//------------------------------Value-----------------------------------------
// An add node sums it's two _in.  If one input is an RSD, we must mixin
// the other input's symbols.
const Type* AddNode::Value(PhaseGVN* phase) const {
  // Either input is TOP ==> the result is TOP
  const Type* t1 = phase->type(in(1));
  const Type* t2 = phase->type(in(2));
  if (t1 == Type::TOP || t2 == Type::TOP) {
    return Type::TOP;
  }

  // Check for an addition involving the additive identity
  const Type* tadd = add_of_identity(t1, t2);
  if (tadd != nullptr) {
    return tadd;
  }

  return add_ring(t1, t2);               // Local flavor of type addition
}

//------------------------------add_identity-----------------------------------
// Check for addition of the identity
const Type *AddNode::add_of_identity( const Type *t1, const Type *t2 ) const {
  const Type *zero = add_id();  // The additive identity
  if( t1->higher_equal( zero ) ) return t2;
  if( t2->higher_equal( zero ) ) return t1;

  return nullptr;
}

AddNode* AddNode::make(Node* in1, Node* in2, BasicType bt) {
  switch (bt) {
    case T_INT:
      return new AddINode(in1, in2);
    case T_LONG:
      return new AddLNode(in1, in2);
    default:
      fatal("Not implemented for %s", type2name(bt));
  }
  return nullptr;
}

bool AddNode::is_not(PhaseGVN* phase, Node* n, BasicType bt) {
  return n->Opcode() == Op_Xor(bt) && phase->type(n->in(2)) == TypeInteger::minus_1(bt);
}

AddNode* AddNode::make_not(PhaseGVN* phase, Node* n, BasicType bt) {
  switch (bt) {
    case T_INT:
      return new XorINode(n, phase->intcon(-1));
    case T_LONG:
      return new XorLNode(n, phase->longcon(-1L));
    default:
      fatal("Not implemented for %s", type2name(bt));
  }
  return nullptr;
}

/* Simplify linear combination of nodes directly into canonical shape.
 *
 * # What
 * It transforms trees made of AddX/SubX (where X is either I and L) whose leaves are either:
 * - MulX(a, b) where there is at least one constant among a and b
 * - LShiftX(a, b) where b is a constant
 * - other kind of nodes, including constants.
 *
 * Overall, one can compute the symbolic value of this kind of trees under the form:
 * c_1 * N_1 + c_2 * N_2 + ... + c_n * N_n + K
 * where c_i and K are constants, N_i are other kind of nodes (non-constants, not multiplication by a constant,
 * not left-shift by a constant). This might be a bit awkward to call that linear combination since we have a
 * constant K, but the term "affine combination" designates something else.
 *
 * # Goals
 * The idea is to compute symbolically the value of such a tree, and dump it in canonical shape at once,
 * including simplification. We will define the canonical shape later, but the canonical representation
 * of a linear combination is not necessarily unique.
 * But it does it with smartness:
 * - since computing the symbolic value of a AddX/SubX needs to compute the symbolic values of the
 *   operands we also replace these nodes with their canonical version.
 * - for the tree T = AddX(A, B), let's call A' (resp. B') the canonical representation of A (resp. B),
 *   If the tree T' := AddX(A', B') is already in canonical shape, we transform T into T'. This allows
 *   to reuse more nodes than building a canonical shape from the symbolic value of T. For instance, let
 *   T be the tree (a + b) + (c + d). Moreover, let A := a + b and B := c + d, that are already in
 *   canonical representation. The symbolic value of T is a + b + c + d. The simpler tree to build for
 *   this expression would be ((a + b) + c) + d, but since (a + b) + (c + d) is also canonical, it is
 *   better to pick the latter expression as it reuses the nodes A and B. In particular, an expression in
 *   canonical shape must not be change, and the algorithm must create no node.
 * - it makes multiplications by constants into a nice shape when possible.
 *
 * # Canonical Shapes
 * Canonical shapes favor additions over subtractions, get the constants close from the root, and put
 * negative signs into constants instead of subtractions. The toplevel shape must be either:
 * 1. (p - n) + c
 * 2. p - n
 * 3. c - n
 * 4. p + c
 * 5. 0 - n
 * 6. p
 * 7. c
 * where:
 * - p (positive terms) is a tree of AddX whose leaves are defined thereafter
 * - n (negative terms) is a tree of AddX whose leaves are defined thereafter
 * - c is a ConX node
 * Leaves in p and n are either:
 * 1. a non-special node (denotes "a" in the next cases), or a preserved sub-tree.
 * 2. LShiftX(a, c) where c is a constant with c > 0, for terms of the form "2^c * a"
 * 3. AddX(LShiftX(a, c1), LShiftX(a, c2)) where c1 and c2 are constants with c1 > c2 > 0,
 *    for terms of the form "(2^c1 + 2^c2) * a"
 *    The bound is tight:
 *    - for c1 = c2, 2^c1 + 2^c2 = 2*2^c1 = 2^(c1 + 1), that is case 2.
 * 4. AddX(LShiftX(a, c), a) where c is a constant with c > 0, for terms of the form (2^c + 0) * a
 * 5. SubX(LShiftX(a, c1), LShiftX(a, c2)) where c1 and c2 are constants with c1 > c2 + 2 and c2 > 0,
 *    for terms of the form "(2^c1 - 2^c2) * a"
 *    The bound is tight:
 *    - for c1 = c2 + 1, 2^c1 - 2^c2 = 2*2^c2 - 2^c2 = 2^c2, that is case 2.
 *    - for c1 = c2 + 2, 2^c1 - 2^c2 = 4*2^c2 - 2^c2 = 3*2^c2 = 2^(c2+1) + 2^c1, that is case 3.
 * 6. SubX(LShiftX(a, c), a) where c is a constant with c > 1, for terms of the form "(2^c - 1) * a".
 * 7. MulX(c, a), where c is a constant with |c| > 1, only in the positive terms "p".
 *
 * ## Example
 * - 5*A + 9*B + 11*C - 11*D + E + 7*F + 14*G - 9*H - 10*I - J - 15*K - 28*L + 42 - 1337
 *   => ( (A<<2 + A) + (B<<3 + B<<1) + 11*C + (-11)*D + E + (F<<3 - F) + (G<<4 - G<<1) )
 *    - ( (H<<3 + H) + (I<<3 + I<<2) + J + (K<<4 - K) + (L<<5 - L<<2) )
 *    + (-1295)
 *  The parentheses inside the "p" and "n" parts (first and second lines) can be put arbitrarily.
 *
 * # Preserved sub-trees
 * Some sub-trees are not transformed, but are not atomic and can still be evaluated. There are 2 cases at the moment:
 * - expressions of the form 3. to 6. above: we can turn them into a term, and dump it correctly again, but that would be
 *   useless work. If we identify them early, we can simply prevent useless transformation.
 * - cases of the form "(x + C) - v" or "v - (x + C)" where the addition is a loop increment and "v" is a induction variable.
 *   See ok_to_convert_loop for details.
 *
 * In any case, we may be able to optimize a super-tree. For instance, if we have:
 * T1 := (x + C) - v
 * T2 := T1 - C
 * T3 := T1 + v
 * We should not replace T1 where it is used outside of the Add/Sub tree, but T2 can be replaced by "x - v",
 * and T3 can be replaced by "x". To replace T2 and T3, we need to be aware of the symbolic value of T1, even if we leave it be.
 *
 * # Algorithm
 * The algorithm is essentially a DFS in two steps with memoization. The memory is morally a mapping
 * from nodes to their linear combination, a node in the canonical representation (possible itself),
 * and whether doing so lead to an improvement of the expression.
 *
 * We start with a stack containing only the node at the root of the sub-tree we want to transform, in
 * pre-traversal state.
 *
 * We pop the top of the stack (noted n) with its traversal state. If the node is marked as done, we skip it.
 *
 * In Pre-traversal state:
 *   We check the shape of the tree around n. There are 3 cases:
 *   - n has good shape and may be transformed, then we stack n for post-traversal with replacement,
 *     and we stack the operands of n (so they are treated before) in pre-traversal state.
 *   - n has good shape but must not be transformed, then we stack n for post-traversal without replacement,
 *     and we stack the operands of n (so they are treated before) in pre-traversal state.
 *   - n has no special shape => we map n to the linear combination 1 * n. We mark n as done.
 *
 * In Post-traversal, without replacement:
 *   We get the linear combination associated with the operands of n, we compute the combination for n
 *   and we save it. We also save whether computing the symbolic expression for n leads to an improvement.
 *   This happens if the symbolic expression of an operand is already an improvement, or if combining operands
 *   allows some factorization.
 *
 *   Node n is marked done.
 *
 * In Post-traversal, with replacement:
 *   This case is only reached for AddX/SubX nodes. Let's say without loss of generality that n = AddX(l, r).
 *
 *   We get the linear combination associated with the operands of n, we compute the combination for n and
 *   whether this is an improvement. We write Cl (resp. Cr) the symbolic combination for l (resp. r), and l'
 *   (resp. r') the computed representation of l (resp. r). Let C = Cl + Cr.
 *   There are 3 cases:
 *   - AddX(l', r') is in canonical form, Cl or Cr have been an improvement but Cl + Cr leads to no further
 *     improvement => we map n to the combination C, node n' := AddX(l', r'), and call it an improvement
 *   - Cl + Cr leads to an improvement or AddX(l', r') is not in canonical form => we build a canonical node n'
 *     for the symbolic value C, we map n to C, the node n', and we call it an improvement.
 *   - otherwise (neither Cl, Cr or C has an improvement, AddX(l', r') is in canonical form), we simply map n
 *     to itself, with combination C, and make it as not improved. In this case, n' := n.
 *
 *   Afterwards, we check whether n != n', if so remember that the function progressed. We also check whether
 *   n is the root node, the first in the stack; if so, we remember n' as being the returned value of ::Ideal.
 *   If n is not this root node, in IGVN only, we replace n by n'. Because of this replacement, in IGVN,
 *   everywhere we say "we map n to n'", we actually map n' to n', since when we will visit the nodes deeper
 *   on the stack, we will have replaced the input n with n'.
 *
 *   Node n is marked done.
 *
 * Once the stack is empty:
 * if the function did not progress, we return nullptr
 * otherwise, if n' is not an old node, or if n == n', we return n'
 * otherwise (the function progressed, but n' is an old node and n != n') we return n + 0,
 *   to make IGVN verification happy, while making it easy to transform to n (by ::Identity), and without
 *   redoing the traversal in ::Identity.
 *
 * # The Notion of Improvement
 *
 * Let A and B be linear combinations. Intuitively, we say that A +/- B makes an improvement when putting the
 * terms from A and B next to each other isn't the best one can do. For instance, in the sum (a + b) + (a + c),
 * we can factor the a. In the difference (a + b) - (2 * a + c), we can cancel out some a. More precisely, we
 * have an improvement if any of the following is true:
 * - there is a term for the same node both in A and B
 * - constant components of A and B are both non-null
 * - constant component of B is non-null, and we are computing A - B (since we want to replace 0 - c by (-c))
 *
 * # Examples
 * In post-traversal state, with replacement, if we have:
 * - op=AddX, l=(a + b), r=(c + d), no improvement in l and r =>
 *   AddX(l, r) is canonical, n is not improved, we don't touch anthing
 * - op=AddX, l=(a + b), r=(c + a), no improvement in l and r =>
 *   the combination for n is 2*a + b + c which is an improvement, so we rebuild the node for this combination:
 *   n':=AddX(AddX(2*a, b), c)
 * - op=AddX, l=(a + b), r=(c - d), no improvement in l and r =>
 *   the combination for n is a + b + c - d which is not an improvement. But n is not in canonical shape (Sub as
 *   input of Add), so we rebuild the node for this combination:
 *   n':=SubX(AddX(AddX((a, b), c), d)
 * - op=AddX, l=(a + b), r=(c + d), improvement in l or r =>
 *   AddX(l, r) is canonical, we build n':=AddX(l, r) and it replaces n.
 *
 * # Debugging
 * The working of all of that can look subtle, or complicated. In debug build, set print_steps_ to true to get
 * more logging. It's a bit verbose. Beware!
 */
class LinearCombination {
  BasicType bt_;
  PhaseGVN& gvn_;
#ifndef PRODUCT
public:
  bool print_steps_ = false;
private:
#endif

  struct StackItem {
    enum class TraversalState { Pre, PostAndReplace, PostNoReplace };

    Node* node;
    TraversalState state;

    static StackItem first_visit(Node* n) { return StackItem {n, TraversalState::Pre}; }
    static StackItem second_visit(Node* n, bool replace) {
      if (replace) {
        return StackItem {n, TraversalState::PostAndReplace};
      }
      return StackItem {n, TraversalState::PostNoReplace};
    }
  };

  class Stack {
    // Nodes of the worklist that are enqueued for a second visit.
    // Finding this node in first visit means that it is a transitive input of itself, that is, we have a dead data loop.
    Unique_Node_List second_visit_pending_;
    // Fully processed nodes for which the canonical node and results are available
    Unique_Node_List done_;
    // Fully processed nodes that were replaced, and should not be in the graph. They can still exist in the stack if they
    // were enstacked multiple times in pre-traversal state.
    Unique_Node_List killed_;
    GrowableArray<StackItem> worklist_;

  public:
    NOT_PRODUCT(bool print_steps_ = false;)

    Stack(Node* n) {
#ifndef PRODUCT
      if (print_steps_) {
        tty->print_cr("New worklist");
      }
#endif
      push_first_visit(n);
    }

    void push_first_visit(Node* n) {
      precond(!killed_.member(n));
      assert(!second_visit_pending_.member(n), "dead loop detected");
      if (!done_.member(n)) {
#ifndef PRODUCT
        if (print_steps_) {
          tty->print("  Push first visit: ");
          n->dump();
        }
#endif
        worklist_.push(StackItem::first_visit(n));
      } else {
#ifndef PRODUCT
        if (print_steps_) {
          tty->print("  Already enqueued for first visit: ");
          n->dump();
        }
#endif
      }
    }

    void push_second_visit_to_replace(Node* n) {
      precond(!second_visit_pending_.member(n));
      precond(!done_.member(n));
      precond(!killed_.member(n));
      second_visit_pending_.push(n);
      worklist_.push(StackItem::second_visit(n, true));
#ifndef PRODUCT
      if (print_steps_) {
        tty->print("  Push second visit to replace: ");
        n->dump();
      }
#endif
    }

    void push_second_visit_without_replace(Node* n) {
      precond(!second_visit_pending_.member(n));
      precond(!done_.member(n));
      precond(!killed_.member(n));
      second_visit_pending_.push(n);
      worklist_.push(StackItem::second_visit(n, false));
#ifndef PRODUCT
      if (print_steps_) {
        tty->print("  Push second visit no replace: ");
        n->dump();
      }
#endif
    }

  private:
    void remove_done_top_of_stack() {
      while (!worklist_.is_empty()) {
        const StackItem& item = worklist_.top();
        if (done_.member(item.node)) {
#ifndef PRODUCT
          if (print_steps_) {
            tty->print("  Popping following done node (state=%d): ", static_cast<int>(item.state));
            item.node->dump();
          }
#endif
          worklist_.pop();
        } else if (killed_.member(item.node)) {
#ifndef PRODUCT
          if (print_steps_) {
            tty->print("  Popping following killed node (state=%d): ", static_cast<int>(item.state));
            item.node->dump();
          }
#endif
          worklist_.pop();
        } else {
          return;
        }
      }
    }

  public:
    [[nodiscard]] bool is_nonempty() const {
      return worklist_.is_nonempty();
    }

    StackItem pop() {
      StackItem item = worklist_.pop();
      assert(item.state == StackItem::TraversalState::Pre || second_visit_pending_.member(item.node), "should have been in the pending list");
      assert(item.state != StackItem::TraversalState::Pre || !second_visit_pending_.member(item.node), "should not be in the pending list");
      second_visit_pending_.remove(item.node);
#ifndef PRODUCT
      if (print_steps_) {
        tty->print("Popping (state=%d): ", static_cast<int>(item.state));
        item.node->dump();
      }
#endif
      remove_done_top_of_stack();
      return item;
    }

    void done(Node* n) {
      done_.push(n);
#ifndef PRODUCT
      if (print_steps_) {
        tty->print("  Done: ");
        n->dump();
      }
#endif
      remove_done_top_of_stack();
    }

    void killed(Node* n) {
      killed_.push(n);
#ifndef PRODUCT
      if (print_steps_) {
        tty->print("  Killed: ");
        n->dump();
      }
#endif
      remove_done_top_of_stack();
    }
  };

  struct Term {
    jlong scalar_;
    Node* vector_;

    [[nodiscard]] Term negate() const {
      return {java_negate(scalar_), vector_};
    }

    void dump(outputStream* out) const {
      out->print("%ld * <%d>", scalar_, vector_->_idx);
    }
  };

  [[nodiscard]] bool is_constant(Node* n) const {
    const TypeInteger* t = gvn_.type(n)->isa_integer(bt_);
    return t != nullptr && t->is_con();
  }

  [[nodiscard]] bool is_int_constant(Node* n) const {
    const TypeInt* t = gvn_.type(n)->isa_int();
    return t != nullptr && t->is_con();
  }

  [[nodiscard]] bool is_constant(Node* n, jlong expected) const {
    jlong actual;
    if (!is_and_get_constant(n , actual)) {
      return false;
    }
    return is_con(actual, expected);
  }

  [[nodiscard]] bool is_and_get_constant(Node* n, jlong& val) const {
    if (const TypeInteger* t = gvn_.type(n)->isa_integer(bt_); t != nullptr && t->is_con()) {
      val = t->get_con_as_long(bt_);
      return true;
    }
    return false;
  }

  [[nodiscard]] bool is_and_get_int_constant(Node* n, jint& val) const {
    if (const TypeInt* t = gvn_.type(n)->isa_int(); t != nullptr && t->is_con()) {
      val = t->get_con();
      return true;
    }
    return false;
  }

  [[nodiscard]] jlong get_constant(Node* n) const {
    const TypeInteger* t = gvn_.type(n)->isa_integer(bt_);
    assert(t != nullptr, "must have a type");
    assert(t->is_con(), "must be a constant");
    return t->get_con_as_long(bt_);
  }

  [[nodiscard]] jint get_int_constant(Node* n) const {
    const TypeInt* t = gvn_.type(n)->isa_int();
    assert(t != nullptr, "must have a type");
    assert(t->is_con(), "must be a constant");
    return t->get_con();
  }

  struct Combination {
    BasicType bt_;
    GrowableArray<Term> combination_;
    jlong constant_;

  private:
    explicit Combination(BasicType bt) : bt_(bt), constant_(0) {}
    explicit Combination(BasicType bt, jlong constant) : bt_(bt), constant_(constant) {}
    explicit Combination(const LinearCombination* lc, jlong scalar, Node* vector) : bt_(lc->bt_) {
      if (jlong con_val; lc->is_and_get_constant(vector, con_val)) {
        constant_ = java_multiply(scalar, con_val);
      } else {
        combination_.push(Term{scalar, vector});
        constant_ = 0;
      }
    }
  public:
    static Combination zero(BasicType bt) {
      return Combination(bt);
    }
    static Combination make_term(const LinearCombination* lc, jlong scalar, Node* vector) {
      return Combination(lc, scalar, vector);
    }
    static Combination make_constant(BasicType bt, jlong constant) {
      return Combination(bt, constant);
    }

    static int compare_terms(const Term& lhs, const Term& rhs) {
      return static_cast<int>(lhs.vector_->_idx - rhs.vector_->_idx);
    }
    static int compare_node_term(const Node* const& lhs, const Term& rhs) {
      return static_cast<int>(lhs->_idx - rhs.vector_->_idx);
    }

    [[nodiscard]] bool is_con(jlong x, jlong con) const {
      return LinearCombination::is_con(bt_, x, con);
    }

    [[nodiscard]] bool is_zero() const {
      for (const Term& term: combination_) {
        if (!is_con(term.scalar_, 0)) {
          return false;
        }
      }
      return is_con(constant_, 0);
    }

    [[nodiscard]] Combination sum(const Combination& other, const bool neg, bool& improves) const {
      Combination result(bt_);
      result.combination_.appendAll(&this->combination_);
      for (const Term& new_term : other.combination_) {
        result.sum(new_term, neg, improves);
      }
      // Constant in both operands can be added. In case of a subtraction, we can rather flip the sign
      // of the constant.
      if ((constant_ != 0 && other.constant_ != 0) || (neg && other.constant_ != 0)) {
        improves = true;
      }
      if (neg) {
        result.constant_ = java_subtract(constant_, other.constant_);
      } else {
        result.constant_ = java_add(constant_, other.constant_);
      }
      // If any operands is zero, we can simply omit the sum.
      improves = improves || (!neg && is_zero()) || other.is_zero();
      return result;
    }

    void sum(const Term& new_term, const bool neg, bool& improves) {
      bool found;
      int location = combination_.find_sorted<Term, compare_terms>(new_term, found);
      if (!found) {
        if (neg) {
          combination_.insert_before(location, new_term.negate());
        } else {
          combination_.insert_before(location, new_term);
        }
      } else {
        jlong& scalar = combination_.at(location).scalar_;
        if (neg) {
          scalar = java_subtract(scalar, new_term.scalar_);
        } else {
          scalar = java_add(scalar, new_term.scalar_);
        }
        // A term present in both side can be factored
        improves = true;
      }
    }

    [[nodiscard]] Combination scalar_multiplication(jlong scalar) const {
      if (is_con(scalar, 0)) {
        return zero(bt_);
      }
      if (is_con(scalar, 1)) {
        return *this;
      }

      Combination result(bt_);
      for (const Term& term : combination_) {
        Term new_term{java_multiply(scalar, term.scalar_), term.vector_};
        result.combination_.push(new_term);
      }

      result.constant_ = java_multiply(scalar, constant_);
      return result;
    }

    void dump(outputStream* out) const {
      bool first = true;
      for (const Term& term: combination_) {
        if (!first) {
          out->print(" + ");
        }
        first = false;
        term.dump(out);
      }
      if (!first) {
        out->print(" + ");
      }
      out->print("%ld", constant_);
    }

    [[nodiscard]] bool is_simple_enough() const {
      int non_zero_terms = 0;
      for (const Term& term: combination_) {
        if (!is_con(term.scalar_, 0)) {
          non_zero_terms++;
        }
        if (non_zero_terms > 2) {
          return false;
        }
      }
      return true;
    }
  };

  struct Result {
    const Node* node_;
    Combination combination_;
    Node* canonical_node_;
    bool improved_;

    Result() : node_(nullptr), combination_(Combination::zero(T_ILLEGAL)), canonical_node_(nullptr), improved_(false) {}

    Result(const Node* node, const Combination& combination, Node* canonical_node, bool improved)
      : node_(node),
        combination_(combination),
        canonical_node_(canonical_node),
        improved_(improved) {}

    void dump(outputStream* out) const {
      out->print("%d => ", node_->_idx);
      combination_.dump(out);
      out->print(" = [%d] (improved=%d)", canonical_node_->_idx, improved_);
    }
  };

  void map_node_to_term(GrowableArray<Result>& computed, Node* n, jlong scalar, Node* vector) const {
#ifndef PRODUCT
    if (print_steps_) {
      tty->print("  Mapping node %d to term %ld * ", n->_idx, scalar);
      vector->dump();
    }
#endif
    Combination combination = Combination::make_term(this, scalar, vector);
    computed.push(Result(n, combination, n, false));
  }

  void map_node_to_constant(GrowableArray<Result>& computed, Node* n, jlong constant) const {
#ifndef PRODUCT
    if (print_steps_) {
      tty->print_cr("  Mapping node %d to constant %ld", n->_idx, constant);
    }
#endif
    Combination combination = Combination::make_constant(bt_, constant);
    Node* canonical = bt_ == T_INT ? static_cast<Node*>(gvn_.intcon(static_cast<jint>(constant))) : gvn_.longcon(constant);
    computed.push(Result(n, combination, canonical, false));
  }

  Result find_result(GrowableArray<Result> computed, const Node* n) const {
    int idx = computed.find_if([&](const Result& r) -> bool { return r.node_ == n; });
    assert(idx >= 0, "");
    Result r = computed.at(idx);
#ifndef PRODUCT
    if (print_steps_) {
      tty->print("  Looking up result for node %d: ", n->_idx);
      r.dump(tty);
      tty->cr();
    }
#endif
    return r;
  }

  [[nodiscard]] Node* make_con(jlong con) const {
    if (bt_ == T_INT) {
      return gvn_.intcon(static_cast<jint>(con));
    }
    return gvn_.longcon(con);
  }

  [[nodiscard]] static bool is_con(BasicType bt, jlong x, jlong con) {
    return (bt == T_INT && static_cast<jint>(x) == static_cast<jint>(con)) || (bt == T_LONG && x == con);
  }

  [[nodiscard]] bool is_con(jlong x, jlong con) const {
    return is_con(bt_, x, con);
  }

  [[nodiscard]] Node* transform(Node* n) const {
    if (PhaseIterGVN* igvn = gvn_.is_IterGVN(); igvn != nullptr) {
      return igvn->register_new_node_with_optimizer(n);
    }
    Node* nn = gvn_.transform(n);
    return nn;
  }

  [[nodiscard]] Node* make_lshift(Node* op, int con) const {
    if (con == 0) {
      return op;
    }
    return transform(LShiftNode::make(op, gvn_.intcon(con), bt_));
  }

  [[nodiscard]] Node* add_node(Node* result, Node* new_node) const {
    if (result == nullptr) {
      return new_node;
    }
    return transform(AddNode::make(result, new_node, bt_));
  }

  struct NodeAndSign {
    Node* node_;
    bool is_neg_;
  };
  [[nodiscard]] NodeAndSign node_of_combination_on_pattern(const Combination& c, Node* replaced, Unique_Node_List& nodes_left_to_insert) const {
    int op = replaced->Opcode();

    if (op == Op_Add(bt_) || op == Op_Sub(bt_)) {
      auto lhs = node_of_combination_on_pattern(c, replaced->in(1), nodes_left_to_insert);
      auto rhs = node_of_combination_on_pattern(c, replaced->in(2), nodes_left_to_insert);
      if (lhs.node_ == nullptr && rhs.node_ == nullptr) {
        return {nullptr, false};
      } else if (lhs.node_ == nullptr) {
        return rhs;
      } else if (rhs.node_ == nullptr) {
        return lhs;
      }
      if (lhs.is_neg_ == rhs.is_neg_) {
        return {transform(AddNode::make(lhs.node_, rhs.node_, bt_)), lhs.is_neg_};
      } else if (rhs.is_neg_) {
        return {transform(SubNode::make(lhs.node_, rhs.node_, bt_)), false};
      } else {
        return {transform(SubNode::make(rhs.node_, lhs.node_, bt_)), false};
      }
    } else if (op == Op_Mul(bt_) && (is_constant(replaced->in(1)) || is_constant(replaced->in(2)))) {
      if (is_constant(replaced->in(1))) {
        return node_of_combination_on_pattern(c, replaced->in(2), nodes_left_to_insert);
      } else {
        return node_of_combination_on_pattern(c, replaced->in(1), nodes_left_to_insert);
      }
    } else if (op == Op_LShift(bt_) && is_int_constant(replaced->in(2))) {
      return node_of_combination_on_pattern(c, replaced->in(1), nodes_left_to_insert);
    } else {
      if (!nodes_left_to_insert.member(replaced)) {
        return {nullptr, false};
      } else {
        bool found;
        int location = c.combination_.find_sorted<const Node*, Combination::compare_node_term>(replaced, found);
        assert(found, "must be in there");
        nodes_left_to_insert.remove(replaced);
        return node_of_term(c.combination_.at(location));
      }
    }
  }

  [[nodiscard]] Node* node_of_combination_on_pattern(const Combination& c, Node* replaced) const {
    Unique_Node_List nodes_left_to_insert;
    for (const Term& term: c.combination_) {
      if (!is_con(term.scalar_, 0)) {
        nodes_left_to_insert.push(term.vector_);
      }
    }
    NodeAndSign new_tree = node_of_combination_on_pattern(c, replaced, nodes_left_to_insert);
#ifdef ASSERT
    if (nodes_left_to_insert.size() != 0) {
      stringStream ss;
      ss.print("combination: ");
      c.dump(&ss);
      ss.print("; node left:");
      for (uint i = 0; i < nodes_left_to_insert.size(); ++i) {
        ss.print(" %d",  nodes_left_to_insert.at(i)->_idx);
      }
#ifndef PRODUCT
      ss.print("; subgraph: ");
      dump_sub_graph(&ss, replaced);
#endif
      assert(nodes_left_to_insert.size() == 0, "should have been consumed: %s", ss.base());
    }
#endif
    if (is_con(c.constant_, 0)) {
      if (new_tree.node_ == nullptr) {
        return gvn_.zerocon(bt_);
      }
      if (new_tree.is_neg_) {
        return transform(SubNode::make(gvn_.zerocon(bt_), new_tree.node_, bt_));
      }
      return new_tree.node_;
    } else {
      if (new_tree.node_ == nullptr) {
        return make_con(c.constant_);
      }
      if (new_tree.is_neg_) {
        return transform(SubNode::make(make_con(c.constant_), new_tree.node_, bt_));
      }
      return transform(AddNode::make(new_tree.node_, make_con(c.constant_), bt_));
    }
  }

  [[nodiscard]] NodeAndSign node_of_term(const Term &term) const {
    if (is_con(term.scalar_, 0)) {
      return {nullptr, false};
    }

    MulNode::IntegerAsSumOrDiffOfPowerOf2 decomposed =
        bt_ == T_INT
          ? MulNode::decompose_jint(static_cast<jint>(term.scalar_))
          : MulNode::decompose_jlong(term.scalar_);

    if (decomposed.does_not_have_nice_shape()) {
      Node *con = make_con(term.scalar_);
      Node *mul = transform(MulNode::make(con, term.vector_, bt_));
      return {mul, false};
    }

    if (decomposed.is_simple_power_of_two()) {
      Node *term_node = make_lshift(term.vector_, decomposed.high_bit());
      return {term_node, decomposed.sign_flip()};
    } else {
      Node *h = make_lshift(term.vector_, decomposed.high_bit());
      Node *l = make_lshift(term.vector_, decomposed.low_bit());
      if (decomposed.is_sum()) {
        Node *term_node = transform(AddNode::make(h, l, bt_));
        return {term_node, decomposed.sign_flip()};
      } else {
        Node *term_node;
        if (decomposed.sign_flip()) {
          term_node = transform(SubNode::make(l, h, bt_));
        } else {
          term_node = transform(SubNode::make(h, l, bt_));
        }
        return {term_node, false};
      }
    }
  }

  [[nodiscard]] Node* node_of_combination(const Combination& c) const {
    Node* positive_terms_node = nullptr;
    Node* negative_terms_node = nullptr;
    Node* constant_node = nullptr;

    for (const auto& term: c.combination_) {
      NodeAndSign term_node = node_of_term(term);

      if (term_node.node_ != nullptr) {
        if (term_node.is_neg_) {
          negative_terms_node = add_node(negative_terms_node, term_node.node_);
        } else {
          positive_terms_node = add_node(positive_terms_node, term_node.node_);
        }
      }
    }
    if (is_con(c.constant_, 0)) {
      constant_node = nullptr;
    } else {
      constant_node = make_con(c.constant_);
    }

    if (constant_node == nullptr) {
      if (positive_terms_node == nullptr) {
        if (negative_terms_node == nullptr) {  // 0
          return gvn_.zerocon(bt_);
        } else {  // 0 - n
          Node* ret = transform(SubNode::make(gvn_.zerocon(bt_), negative_terms_node, bt_));
          return ret;
        }
      } else {
        if (negative_terms_node == nullptr) {  // p
          return positive_terms_node;
        } else {  // p - n
          Node* ret = transform(SubNode::make(positive_terms_node, negative_terms_node, bt_));
          return ret;
        }
      }
    } else {
      if (positive_terms_node == nullptr) {
        if (negative_terms_node == nullptr) {  // c
          return constant_node;
        } else {  // c - n
          Node* ret = transform(SubNode::make(constant_node, negative_terms_node, bt_));
          return ret;
        }
      } else {
        if (negative_terms_node == nullptr) {  // p + c
          Node* ret = transform(AddNode::make(positive_terms_node, constant_node, bt_));
          return ret;
        } else {  // p - n + c
          Node* diff = transform(SubNode::make(positive_terms_node, negative_terms_node, bt_));
          Node* ret = transform(AddNode::make(diff, constant_node, bt_));
          return ret;
        }
      }
    }
  }

  [[nodiscard]] static bool is_cloop_increment(const Node* inc) {
    precond(inc->Opcode() == Op_AddI || inc->Opcode() == Op_AddL);

    if (!inc->in(1)->is_Phi()) {
      return false;
    }
    const PhiNode* phi = inc->in(1)->as_Phi();

    if (!phi->region()->is_CountedLoop()) {
      return false;
    }

    return inc == phi->region()->as_CountedLoop()->incr();
  }

  // Given the expression '(x + C) - v', or
  //                      'v - (x + C)', we examine nodes '+' (inc) and 'v' (var):
  //
  //  1. Do not convert if '+' is a counted-loop increment, because the '-' is
  //     loop invariant and converting extends the live-range of 'x' to overlap
  //     with the '+', forcing another register to be used in the loop.
  //
  //  2. Do not convert if 'v' is a counted-loop induction variable, because
  //     'x' might be invariant.
  //
  [[nodiscard]] static bool ok_to_convert_loop(Node* inc, const Node* var) {
    return !(is_cloop_increment(inc) || var->is_cloop_ind_var());
  }
public:
  [[nodiscard]] bool ok_to_convert_multiplication_as_shift(const Node* n) const {
    int op = n->Opcode();
    if (op != Op_Add(bt_) && op != Op_Sub(bt_)) {
      return true;
    }

    Node* lhs = n->in(1);
    int op_lhs = n->in(1)->Opcode();
    Node* rhs = n->in(2);
    int op_rhs = n->in(2)->Opcode();
    // Do not transform shapes generated by MulNode::Ideal
    // (1) (x << con1) + (x << con2) => simplified from a multiplication by a constant with only two set bits
    // (2) (x << con1) + x => special case of (2), when con2 = 0
    // (3) (x << con1) - (x << con2) => simplified from a multiplication by a constant of the form 2^con1 - 2^con2
    // (4) (x << con1) - x => special case of (3) when con2 = 0
    // (5) x - (x << con1) => variation of (4), for negative coefficients
    if (op == Op_Add(bt_) || op == Op_Sub(bt_)) {
      jint l_con, r_con;
      // Case (1) and (3)
      if (
        op_lhs == Op_LShift(bt_) &&
        is_and_get_int_constant(lhs->in(2), l_con) &&
        op_rhs == Op_LShift(bt_) &&
        is_and_get_int_constant(rhs->in(2), r_con) &&
        lhs->in(1) == rhs->in(1)
      ) {
        int con1 = MAX2(l_con, r_con);
        int con2 = MIN2(l_con, r_con);
        // In (x << con1) + (x << con2):
        // con1 == con2 => can be changed into x << (con1 + 1)
        if (op == Op_Add(bt_) && con1 > con2) {
          return false;
        }
        // In (x << con1) - (x << con2):
        // con1 == con2 => can be changed into 0
        // con1 == con2 + 1 => can be changed into x << con2
        // con1 == con2 + 2 => can be changed into x << (con2 + 1) + x << con2
        if (op == Op_Sub(bt_) && con1 > con2 + 2) {
          return false;
        }
      }
    }
    if (op == Op_Add(bt_)) {
      jint con;
      // Case (2)
      // con1 == 0 => can be changed into x << 1
      if (
        (op_lhs == Op_LShift(bt_) && is_and_get_int_constant(lhs->in(2), con) && lhs->in(1) == rhs && con >= 1) ||
        (op_rhs == Op_LShift(bt_) && is_and_get_int_constant(rhs->in(2), con) && rhs->in(1) == lhs && con >= 1)
      ) {
        return false;
      }
    } else if (op == Op_Sub(bt_)) {
      jint con;
      // Case (4)
      // con1 == 0 => can be changed into 0
      // con1 == 1 => can be changed into x
      // con1 == 2 => can be changed into (x << 1) + x
      if (op_lhs == Op_LShift(bt_) && is_and_get_int_constant(lhs->in(2), con) && lhs->in(1) == rhs && con > 2) {
        return false;
      }
      // Case (5)
      // con1 == 0 => can be changed into 0
      // con1 == 1 => can be changed into -x (that is "x" in the negative term)
      // con1 == 2 => can be changed into -((x << 1) + x) (that is "(x << 1) + x" in the negative term)
      if (op_rhs == Op_LShift(bt_) && is_and_get_int_constant(rhs->in(2), con) && rhs->in(1) == lhs && con > 2) {
        return false;
      }
    }

    return true;
  }
private:

  bool ok_to_convert(const Node* n, bool as_root) const {
    int op = n->Opcode();
    Node* lhs = n->in(1);
    int op_lhs = lhs->Opcode();
    Node* rhs = n->in(2);
    int op_rhs = rhs->Opcode();
    // Do not transform (x + c0) - y if "+" is a loop increment or
    // if "y" is a loop induction variable.
    if (op == Op_Sub(bt_)) {
      if (op_lhs == Op_Add(bt_)) {
        if (!ok_to_convert_loop(lhs, rhs)) {
          return false;
        }
      }
      // Same with y - (x + c0)
      if (op_rhs == Op_Add(bt_)) {
        if (!ok_to_convert_loop(rhs, lhs)) {
          return false;
        }
      }
    }

    // cases alike `x << con1 + x << con2` to compute x * (2^con1 + 2^con2)
    if (!ok_to_convert_multiplication_as_shift(n)) {
      return false;
    }
    if (op == Op_Sub(bt_) && is_constant(lhs, 0)) {
      // 0 - [the cases above]
      if (!ok_to_convert_multiplication_as_shift(rhs)) {
        return false;
      }

      // 0 - (x << con)
      if (as_root && op_rhs == Op_LShift(bt_)) {
        return false;
      }
    }
    return true;
  }

#ifndef PRODUCT
  void dump_sub_graph(outputStream* out, Node* n) const {
    int op = n->Opcode();
    if (op == Op_Add(bt_)) {
      out->print("[%d](", n->_idx);
      dump_sub_graph(out,n->in(1));
      out->print(" + ");
      dump_sub_graph(out, n->in(2));
      out->print(")");
    } else if (op == Op_Sub(bt_)) {
      out->print("[%d](", n->_idx);
      dump_sub_graph(out,n->in(1));
      out->print(" - ");
      dump_sub_graph(out, n->in(2));
      out->print(")");
    } else if (op == Op_LShift(bt_) && is_int_constant(n->in(2))) {
      out->print("[%d](", n->_idx);
      dump_sub_graph(out,n->in(1));
      out->print(" << ");
      dump_sub_graph(out, n->in(2));
      out->print(")");
    } else if (op == Op_Mul(bt_) && (is_constant(n->in(1)) || is_constant(n->in(2)))) {
      out->print("[%d](", n->_idx);
      dump_sub_graph(out,n->in(1));
      out->print(" * ");
      dump_sub_graph(out, n->in(2));
      out->print(")");
    } else if (is_constant(n)) {
      const TypeInteger* t = gvn_.type(n)->isa_integer(bt_);
      if (const TypeInt* ti = t->isa_int(); ti != nullptr) {
        out->print("[%d]%d", n->_idx, ti->get_con());
      } else {
        const TypeLong* tl = t->is_long();
        out->print("[%d]%ldL", n->_idx, tl->get_con());
      }
    } else {
      out->print("<%d %s>", n->_idx, n->Name());
    }
  }
#endif

  // Is it nothing more than a "a +/- b" where we can't do anything with "a" and "b"?
  [[nodiscard]] bool is_uninteresting(Node* n) const {
    auto skip_operand = [this](const Node* n) -> bool {
      int op = n->Opcode();
      if (op == Op_Add(bt_) || op == Op_Sub(bt_)) {
        return false;
      }
      if (op == Op_LShift(bt_) && is_int_constant(n->in(2))) {
        return false;
      }
      if (op == Op_Mul(bt_) && (is_constant(n->in(1)) || is_constant(n->in(2)))) {
        return false;
      }
      return true;
    };

    if (n->Opcode() == Op_Sub(bt_) && is_constant(n->in(2))) {
      return false;
    }
    return skip_operand(n->in(1)) && skip_operand(n->in(2));
  }

  [[nodiscard]] bool gluing_makes_canonical(const Node* node, const Result& lhs, const Result& rhs) const {
    int op = node->Opcode();
    int op_l = lhs.canonical_node_->Opcode();
    int op_r = rhs.canonical_node_->Opcode();

    if (
      (op_l == Op_Sub(bt_) && is_constant(lhs.canonical_node_->in(1), 0)) ||
      (op_r == Op_Sub(bt_) && is_constant(rhs.canonical_node_->in(1), 0))
    ) {
#ifndef PRODUCT
      if (print_steps_) {
        tty->print_cr("  Must transform node %d: operand is a (0 - x)", node->_idx);
      }
#endif
      return false;
    }
    if (op == Op_Add(bt_)) {
      if (
        (op_l == Op_Sub(bt_) && !is_constant(rhs.canonical_node_) && ok_to_convert(lhs.canonical_node_, false)) ||
        (op_r == Op_Sub(bt_) && !is_constant(lhs.canonical_node_) && ok_to_convert(rhs.canonical_node_, false))
      ) {
#ifndef PRODUCT
        if (print_steps_) {
          tty->print_cr("  Must transform node %d: subtract inside something that is not constant addition", node->_idx);
        }
#endif
        return false;
      } else if (
        (op_l == Op_Add(bt_) && ok_to_convert(lhs.canonical_node_, false) && (is_constant(lhs.canonical_node_->in(1)) || is_constant(lhs.canonical_node_->in(2)))) ||
        (op_r == Op_Add(bt_) && ok_to_convert(rhs.canonical_node_, false) && (is_constant(rhs.canonical_node_->in(1)) || is_constant(rhs.canonical_node_->in(2))))
      ) {
#ifndef PRODUCT
        if (print_steps_) {
          tty->print_cr("  Must transform node %d: operand of addition is a constant addition", node->_idx);
        }
#endif
        return false;
      }
    } else if (op == Op_Sub(bt_)) {
      if (
        (op_l == Op_Add(bt_) && ok_to_convert(lhs.canonical_node_, false) && (is_constant(lhs.canonical_node_->in(1)) || is_constant(lhs.canonical_node_->in(2)))) ||
        (op_r == Op_Add(bt_) && ok_to_convert(rhs.canonical_node_, false) && (is_constant(rhs.canonical_node_->in(1)) || is_constant(rhs.canonical_node_->in(2))))
      ) {
#ifndef PRODUCT
        if (print_steps_) {
          tty->print_cr("  Must transform node %d: operand of subtract is a constant addition", node->_idx);
        }
#endif
        return false;
      } else if (
        (op_l == Op_Sub(bt_) && ok_to_convert(lhs.canonical_node_, false)) ||
        (op_r == Op_Sub(bt_) && ok_to_convert(rhs.canonical_node_, false))
      ) {
#ifndef PRODUCT
        if (print_steps_) {
          tty->print_cr("  Must transform node %d: operand of subtract is a subtraction", node->_idx);
        }
#endif
        return false;
      }
    }
    return true;
  }

public:
  LinearCombination(BasicType bt, PhaseGVN& gvn) : bt_(bt), gvn_(gvn) {}

  Node* collect_and_replace(Node* n) const {
    ResourceMark rm;
    GrowableArray<Result> computed;
    bool progress = false;
    Node* new_n = nullptr;
    uint old_unique = gvn_.C->unique();
#ifndef PRODUCT
    if (print_steps_) {
      tty->print("Subgraph: ");
      dump_sub_graph(tty, n);
      if (gvn_.is_IterGVN()) {
        tty->print_cr("; phase=IGVN");
      } else {
        tty->print_cr("; phase=parsing");
      }
    }
#endif
    if (is_uninteresting(n)) {
#ifndef PRODUCT
      if (print_steps_) {
        tty->print_cr("  Uninteresting, not doing anything\n\n");
      }
#endif
      return nullptr;
    }
    Stack stack(n);
    NOT_PRODUCT(stack.print_steps_ = print_steps_;)

    while (stack.is_nonempty()) {
      StackItem item = stack.pop();
      Node* node = item.node;
      int op = node->Opcode();

      if (item.state == StackItem::TraversalState::Pre) {
        if (op == Op_Add(bt_) || op == Op_Sub(bt_)) {
          if (ok_to_convert(node, true)) {
            stack.push_second_visit_to_replace(node);
          } else {
            stack.push_second_visit_without_replace(node);
          }
          stack.push_first_visit(node->in(1));
          stack.push_first_visit(node->in(2));
        } else if (op == Op_LShift(bt_) && is_int_constant(node->in(2))) {
          stack.push_second_visit_without_replace(node);
          stack.push_first_visit(node->in(1));
        } else if (op == Op_Mul(bt_) && (is_constant(node->in(1)) || is_constant(node->in(2)))) {
          if (!is_constant(node->in(1))) {
            stack.push_second_visit_without_replace(node);
            stack.push_first_visit(node->in(1));
            map_node_to_term(computed, node->in(2), 1L, node->in(2));
            stack.done(node->in(2));
          } else if (!is_constant(node->in(2))) {
            stack.push_second_visit_without_replace(node);
            stack.push_first_visit(node->in(2));
            map_node_to_term(computed, node->in(1), 1L, node->in(1));
            stack.done(node->in(1));
          } else {
            jlong constant = java_multiply(get_constant(node->in(1)), get_constant(node->in(2)));
            map_node_to_constant(computed, node, constant);
            stack.done(node);
          }
        } else {
          map_node_to_term(computed, node, 1L, node);
          stack.done(node);
        }
      } else if (item.state == StackItem::TraversalState::PostNoReplace) {
        assert(op == Op_Add(bt_) || op == Op_Sub(bt_) || Op_Mul(bt_) || Op_LShift(bt_), "only add, sub and mul should reach the post state");

        if (op == Op_Add(bt_) || op == Op_Sub(bt_)) {
          Result lhs = find_result(computed, node->in(1));
          Result rhs = find_result(computed, node->in(2));
          bool _improved = false;  // We ignore, since we don't want to reshape locally anway.
          Combination combination = lhs.combination_.sum(rhs.combination_, op == Op_Sub(bt_), _improved);
#ifndef PRODUCT
          if (print_steps_) {
            tty->print("  Mapping node %d to combination ", node->_idx);
            combination.dump(tty);
            tty->cr();
          }
#endif
          computed.push(Result(node, combination, node, lhs.improved_ || rhs.improved_));
        } else if (op == Op_Mul(bt_)) {
          assert(is_constant(node->in(1)) || is_constant(node->in(2)), "one operand of Mul must be constant");

          jlong scalar;
          Node* operand_node;
          if (is_and_get_constant(node->in(1), scalar)) {
            operand_node = node->in(2);
          } else {
            scalar = get_constant(node->in(2));
            operand_node = node->in(1);
          }
          Result operand = find_result(computed, operand_node);
          Combination combination = operand.combination_.scalar_multiplication(scalar);
#ifndef PRODUCT
          if (print_steps_) {
            tty->print("  Mapping node %d to combination ", node->_idx);
            combination.dump(tty);
            tty->cr();
          }
#endif
          computed.push(Result(node, combination, node, operand.improved_));
        } else if (op == Op_LShift(bt_)) {
          assert(is_int_constant(node->in(2)), "rhs of LShift must be constant, but got %s", node->in(2)->Name());

          jint shift = get_int_constant(node->in(2));
          jlong scalar = java_shift_left(1L, shift, bt_);
          Result operand = find_result(computed, node->in(1));
          Combination combination = operand.combination_.scalar_multiplication(scalar);
#ifndef PRODUCT
          if (print_steps_) {
            tty->print("  Mapping node %d to combination ", node->_idx);
            combination.dump(tty);
            tty->cr();
          }
#endif
          computed.push(Result(node, combination, node, operand.improved_));
        } else {
          ShouldNotReachHere();
        }
        stack.done(node);
      } else if (item.state == StackItem::TraversalState::PostAndReplace) {
        assert(op == Op_Add(bt_) || op == Op_Sub(bt_), "only add and sub should reach the post state");

        Result lhs = find_result(computed, node->in(1));
        Result rhs = find_result(computed, node->in(2));

        bool just_gluing_is_canonical = gluing_makes_canonical(node, lhs, rhs);

        bool improved = false;
        Combination combination = lhs.combination_.sum(rhs.combination_, op == Op_Sub(bt_), improved);
        bool simple_enough = combination.is_simple_enough();

        Node* combination_as_node = nullptr;
        if ((lhs.improved_ || rhs.improved_) && !improved && just_gluing_is_canonical) {
          if (op == Op_Add(bt_)) {
            combination_as_node = transform(AddNode::make(lhs.canonical_node_, rhs.canonical_node_, bt_));
          } else if (op == Op_Sub(bt_)) {
            combination_as_node = transform(SubNode::make(lhs.canonical_node_, rhs.canonical_node_, bt_));
          } else {
            ShouldNotReachHere();
          }
#ifndef PRODUCT
          if (print_steps_) {
            tty->print_cr("  Rebuilding root for node %d: lhs.improved_=%d; rhs.improved_=%d; improved=%d; just_gluing_is_canonical=%d", node->_idx, lhs.improved_, rhs.improved_, improved, just_gluing_is_canonical);
          }
#endif
          improved = true;
        } else if (improved) {
          if (simple_enough || gvn_.is_IterGVN()) {
#ifndef PRODUCT
            if (print_steps_) {
              tty->print("  Rebuilding combination ");
              combination.dump(tty);
              tty->print(" on pattern ");
              dump_sub_graph(tty, node);
              tty->print_cr(" for node %d: lhs.improved_=%d; rhs.improved_=%d; improved=%d; just_gluing_is_canonical=%d", node->_idx, lhs.improved_, rhs.improved_, improved, just_gluing_is_canonical);
            }
#endif
            combination_as_node = node_of_combination_on_pattern(combination, node);
          } else {
#ifndef PRODUCT
            if (print_steps_) {
              tty->print("  Rebuilding combination ");
              combination.dump(tty);
              tty->print_cr(" from scratch for node %d: lhs.improved_=%d; rhs.improved_=%d; improved=%d; just_gluing_is_canonical=%d", node->_idx, lhs.improved_, rhs.improved_, improved, just_gluing_is_canonical);
            }
#endif
            combination_as_node = node_of_combination(combination);
          }
        } else if (!just_gluing_is_canonical && !gvn_.is_IterGVN()) {
#ifndef PRODUCT
          if (print_steps_) {
            tty->print("  Rebuilding combination ");
            combination.dump(tty);
            tty->print_cr(" from scratch for node %d: lhs.improved_=%d; rhs.improved_=%d; improved=%d; just_gluing_is_canonical=%d", node->_idx, lhs.improved_, rhs.improved_, improved, just_gluing_is_canonical);
          }
#endif
          combination_as_node = node_of_combination(combination);
        } else {
          combination_as_node = node;
        }

        if (combination_as_node != node) {
          if (node == n) {
            new_n = combination_as_node;
#ifndef PRODUCT
            if (print_steps_) {
              tty->print_cr("  Replacing root node %d ==> %d", node->_idx, combination_as_node->_idx);
            }
#endif
          } else if (PhaseIterGVN* igvn = gvn_.is_IterGVN(); igvn != nullptr) {
#ifndef PRODUCT
            if (print_steps_) {
              tty->print_cr("  Replacing node %d ==> %d", node->_idx, combination_as_node->_idx);
            }
#endif
            // Even in IGVN, `node` can still survive in the stack for first visit, even tho it is no longer in the graph.
            // We can and must skip it since the user of `node` has now the new input instead.
            stack.killed(node);
            igvn->replace_node(node, combination_as_node);
          } else {
#ifndef PRODUCT
            if (print_steps_) {
              tty->print_cr("  Optimized node %d ==> %d", node->_idx, combination_as_node->_idx);
            }
#endif
          }
          progress = true;
        }
#ifndef PRODUCT
        if (print_steps_) {
          tty->print("  Mapping node %d to combination ", node->_idx);
          combination.dump(tty);
          tty->cr();
        }
#endif
        if (gvn_.is_IterGVN()) {
          computed.push(Result(combination_as_node, combination, combination_as_node, improved));
          // In IGVN, this is the new `node`, that's what the users of `node` will see in their input, and the key they will
          // use to look up in `computed`.
          stack.done(combination_as_node);
        } else {
          computed.push(Result(node, combination, combination_as_node, improved));
          // In GVN, `node` will not be replaced and must be recognized as done as the result can be looked up in `computed`.
          stack.done(node);
        }
      } else {
        ShouldNotReachHere();
      }
    }
    if (new_n == nullptr) {
      new_n = n;
    }
#ifndef PRODUCT
    if (print_steps_) {
      tty->print_cr("Done: progress=%d; %d ==> %d", progress, n->_idx, new_n->_idx);
      dump_sub_graph(tty, new_n);
      tty->cr();
    }
#endif
    if (!progress) {
#ifndef PRODUCT
      if (print_steps_) {
        tty->print_cr("\n");
      }
#endif
      return nullptr;
    }
    if (new_n->_idx >= old_unique || new_n == n) {
#ifndef PRODUCT
      if (print_steps_) {
        tty->print_cr("\n");
      }
#endif
      return new_n;
    }
#ifndef PRODUCT
    if (print_steps_) {
      tty->print_cr("Old node detected. Will return artificial new node.");
      tty->print_cr("\n");
    }
#endif
    const TypeTuple* t = bt_ == T_INT ? TypeTuple::INT_UNARY_TUPLE : TypeTuple::LONG_UNARY_TUPLE;
    Node* tuple = transform(TupleNode::make(t, new_n));
    return new ProjNode(tuple, 0);
  }
};

Node* AddNode::IdealIL(PhaseGVN* phase, bool can_reshape, BasicType bt) {
  Node* in1 = in(1);
  Node* in2 = in(2);
  int op1 = in1->Opcode();
  int op2 = in2->Opcode();
#if 1
  // Fold (con1-x)+con2 into (con1+con2)-x
  if (op1 == Op_Add(bt) && op2 == Op_Sub(bt)) {
    // Swap edges to try optimizations below
    in1 = in2;
    in2 = in(1);
    op1 = op2;
    op2 = in2->Opcode();
  }
  if (op1 == Op_Sub(bt)) {
    const Type* t_sub1 = phase->type(in1->in(1));
    const Type* t_2    = phase->type(in2       );
    if (t_sub1->singleton() && t_2->singleton() && t_sub1 != Type::TOP && t_2 != Type::TOP) {
      return SubNode::make(phase->makecon(add_ring(t_sub1, t_2)), in1->in(2), bt);
    }
    // Convert "(a-b)+(c-d)" into "(a+c)-(b+d)"
    if (op2 == Op_Sub(bt)) {
      // But we don't want to break stuff such as (x << n) - (x << m) as they are just an optimized multiplication.
      LinearCombination lc(bt, *phase);
      if (lc.ok_to_convert_multiplication_as_shift(in1) && lc.ok_to_convert_multiplication_as_shift(in2)) {
        // Check for dead cycle: d = (a-b)+(c-d)
        assert( in1->in(2) != this && in2->in(2) != this,
                "dead loop in AddINode::Ideal" );
        Node* sub = SubNode::make(nullptr, nullptr, bt);
        Node* sub_in1;
        PhaseIterGVN* igvn = phase->is_IterGVN();
        // During IGVN, if both inputs of the new AddNode are a tree of SubNodes, this same transformation will be applied
        // to every node of the tree. Calling transform() causes the transformation to be applied recursively, once per
        // tree node whether some subtrees are identical or not. Pushing to the IGVN worklist instead, causes the transform
        // to be applied once per unique subtrees (because all uses of a subtree are updated with the result of the
        // transformation). In case of a large tree, this can make a difference in compilation time.
        if (igvn != nullptr) {
          sub_in1 = igvn->register_new_node_with_optimizer(AddNode::make(in1->in(1), in2->in(1), bt));
        } else {
          sub_in1 = phase->transform(AddNode::make(in1->in(1), in2->in(1), bt));
        }
        Node* sub_in2;
        if (igvn != nullptr) {
          sub_in2 = igvn->register_new_node_with_optimizer(AddNode::make(in1->in(2), in2->in(2), bt));
        } else {
          sub_in2 = phase->transform(AddNode::make(in1->in(2), in2->in(2), bt));
        }
        sub->init_req(1, sub_in1);
        sub->init_req(2, sub_in2);
        return sub;
      }
    }
    // Convert "(a-b)+(b+c)" into "(a+c)"
    if (op2 == Op_Add(bt) && in1->in(2) == in2->in(1)) {
      assert(in1->in(1) != this && in2->in(2) != this,"dead loop in AddINode::Ideal/AddLNode::Ideal");
      return AddNode::make(in1->in(1), in2->in(2), bt);
    }
    // Convert "(a-b)+(c+b)" into "(a+c)"
    if (op2 == Op_Add(bt) && in1->in(2) == in2->in(2)) {
      assert(in1->in(1) != this && in2->in(1) != this,"dead loop in AddINode::Ideal/AddLNode::Ideal");
      return AddNode::make(in1->in(1), in2->in(1), bt);
    }
  }

  // Convert (con - y) + x into "(x - y) + con"
  if (op1 == Op_Sub(bt) && in1->in(1)->Opcode() == Op_ConIL(bt)
      && in1 != in1->in(2) && !(in1->in(2)->is_Phi() && in1->in(2)->as_Phi()->is_tripcount(bt))) {
    return AddNode::make(phase->transform(SubNode::make(in2, in1->in(2), bt)), in1->in(1), bt);
  }

  // Convert x + (con - y) into "(x - y) + con"
  if (op2 == Op_Sub(bt) && in2->in(1)->Opcode() == Op_ConIL(bt)
      && in2 != in2->in(2) && !(in2->in(2)->is_Phi() && in2->in(2)->as_Phi()->is_tripcount(bt))) {
    return AddNode::make(phase->transform(SubNode::make(in1, in2->in(2), bt)), in2->in(1), bt);
  }
#endif

  // Distributive (also uses commutativity)
  if (op1 == Op_Mul(bt) && op2 == Op_Mul(bt)) {
    Node* add_in1 = nullptr;
    Node* add_in2 = nullptr;
    Node* mul_in = nullptr;

    if (in1->in(1) == in2->in(1)) {
      // Convert "a*b+a*c into a*(b+c)
      add_in1 = in1->in(2);
      add_in2 = in2->in(2);
      mul_in = in1->in(1);
    } else if (in1->in(2) == in2->in(1)) {
      // Convert a*b+b*c into b*(a+c)
      add_in1 = in1->in(1);
      add_in2 = in2->in(2);
      mul_in = in1->in(2);
    } else if (in1->in(2) == in2->in(2)) {
      // Convert a*c+b*c into (a+b)*c
      add_in1 = in1->in(1);
      add_in2 = in2->in(1);
      mul_in = in1->in(2);
    } else if (in1->in(1) == in2->in(2)) {
      // Convert a*b+c*a into a*(b+c)
      add_in1 = in1->in(2);
      add_in2 = in2->in(1);
      mul_in = in1->in(1);
    }

    if (mul_in != nullptr) {
      Node* add = phase->transform(AddNode::make(add_in1, add_in2, bt));
      return MulNode::make(mul_in, add, bt);
    }
  }

  // Convert (x >>> rshift) + (x << lshift) into RotateRight(x, rshift)
  if (Matcher::match_rule_supported(Op_RotateRight) &&
      ((op1 == Op_URShift(bt) && op2 == Op_LShift(bt)) || (op1 == Op_LShift(bt) && op2 == Op_URShift(bt))) &&
      in1->in(1) != nullptr && in1->in(1) == in2->in(1)) {
    Node* rshift = op1 == Op_URShift(bt) ? in1->in(2) : in2->in(2);
    Node* lshift = op1 == Op_URShift(bt) ? in2->in(2) : in1->in(2);
    if (rshift != nullptr && lshift != nullptr) {
      const TypeInt* rshift_t = phase->type(rshift)->isa_int();
      const TypeInt* lshift_t = phase->type(lshift)->isa_int();
      int bits = bt == T_INT ? 32 : 64;
      int mask = bt == T_INT ? 0x1F : 0x3F;
      if (lshift_t != nullptr && lshift_t->is_con() &&
          rshift_t != nullptr && rshift_t->is_con() &&
          ((lshift_t->get_con() & mask) == (bits - (rshift_t->get_con() & mask)))) {
        return new RotateRightNode(in1->in(1), phase->intcon(rshift_t->get_con() & mask), TypeInteger::bottom(bt));
      }
    }
  }

#if 0
  // Collapse addition of the same terms into multiplications.
  Node* collapsed = Ideal_collapse_variable_times_con(phase, bt);
  if (collapsed != nullptr) {
    return collapsed; // Skip AddNode::Ideal() since it may now be a multiplication node.
  }
#endif

  if (Node* r = simplify_whole_tree(can_reshape, phase, bt, this); r != nullptr) {
    return r;
  }

  return AddNode::Ideal(phase, can_reshape);
}

Node* AddNode::simplify_whole_tree(bool can_reshape, PhaseGVN* phase, BasicType bt, Node* n) {
  LinearCombination lc(bt, *phase);
  NOT_PRODUCT(lc.print_steps_ = UseNewCode;)
  Node* new_this = lc.collect_and_replace(n);
  if (new_this != nullptr) {
    return new_this; // Skip AddNode::Ideal() since it may now be a multiplication node.
  }
  return nullptr;
}

// Try to collapse addition of the same terms into a single multiplication. On success, a new MulNode is returned.
// Examples of this conversion includes:
//   - a + a + ... + a => CON*a
//   - (a * CON) + a   => (CON + 1) * a
//   - a + (a * CON)   => (CON + 1) * a
//
// We perform such conversions incrementally during IGVN by transforming left most nodes first and work up to the root
// of the expression. In other words, we convert, at each iteration:
//        a + a + a + ... + a
//     => 2*a + a + ... + a
//     => 3*a + ... + a
//     => n*a
//
// Due to the iterative nature of IGVN, MulNode transformed from first few AddNode terms may be further transformed into
// power-of-2 pattern. (e.g., 2 * a => a << 1, 3 * a => (a << 2) + a). We can't guarantee we'll always pick up
// transformed power-of-2 patterns when term `a` is complex.
//
// Note this also converts, for example, original expression `(a*3) + a` into `4*a` and `(a<<2) + a` into `5*a`. A more
// generalized pattern `(a*b) + (a*c)` into `a*(b + c)` is handled by AddNode::IdealIL().
Node* AddNode::Ideal_collapse_variable_times_con(PhaseGVN* phase, BasicType bt) {
  // We need to make sure that the current AddNode is not part of a MulNode that has already been optimized to a
  // power-of-2 addition (e.g., 3 * a => (a << 2) + a). Without this check, GVN would keep trying to optimize the same
  // node and can't progress. For example, 3 * a => (a << 2) + a => 3 * a => (a << 2) + a => ...
  if (Multiplication::find_power_of_two_addition_pattern(this, bt).is_valid()) {
    return nullptr;
  }

  Node* lhs = in(1);
  Node* rhs = in(2);

  Multiplication mul = Multiplication::find_collapsible_addition_patterns(lhs, rhs, bt);
  if (!mul.is_valid_with(rhs)) {
    // Swap lhs and rhs then try again
    mul = Multiplication::find_collapsible_addition_patterns(rhs, lhs, bt);
    if (!mul.is_valid_with(lhs)) {
      return nullptr;
    }
  }

  Node* con;
  if (bt == T_INT) {
    con = phase->intcon(java_add(static_cast<jint>(mul.multiplier()), 1));
  } else {
    con = phase->longcon(java_add(mul.multiplier(), CONST64(1)));
  }

  return MulNode::make(con, mul.variable(), bt);
}

// Find a pattern of collapsable additions that can be converted to a multiplication.
// When matching the LHS `a * CON`, we match with best efforts by looking for the following patterns:
//     - (1) Simple addition:       LHS = a + a
//     - (2) Simple lshift:         LHS = a << CON
//     - (3) Simple multiplication: LHS = CON * a
//     - (4) Power-of-two addition: LHS = (a << CON1) + (a << CON2)
AddNode::Multiplication AddNode::Multiplication::find_collapsible_addition_patterns(const Node* a, const Node* pattern, BasicType bt) {
  // (1) Simple addition pattern (e.g., lhs = a + a)
  Multiplication mul = find_simple_addition_pattern(a, bt);
  if (mul.is_valid_with(pattern)) {
    return mul;
  }

  // (2) Simple lshift pattern (e.g., lhs = a << CON)
  mul = find_simple_lshift_pattern(a, bt);
  if (mul.is_valid_with(pattern)) {
    return mul;
  }

  // (3) Simple multiplication pattern (e.g., lhs = CON * a)
  mul = find_simple_multiplication_pattern(a, bt);
  if (mul.is_valid_with(pattern)) {
    return mul;
  }

  // (4) Power-of-two addition pattern (e.g., lhs = (a << CON1) + (a << CON2))
  // While multiplications can be potentially optimized to power-of-2 subtractions (e.g., a * 7 => (a << 3) - a),
  // (x - y) + y => x is already handled by the Identity() methods. So, we don't need to check for that pattern here.
  mul = find_power_of_two_addition_pattern(a, bt);
  if (mul.is_valid_with(pattern)) {
    return mul;
  }

  // We've tried everything.
  return make_invalid();
}

// Try to match `n = a + a`. On success, return a struct with `.valid = true`, `variable = a`, and `multiplier = 2`.
// The method matches `n` for pattern: a + a.
AddNode::Multiplication AddNode::Multiplication::find_simple_addition_pattern(const Node* n, BasicType bt) {
  if (n->Opcode() == Op_Add(bt) && n->in(1) == n->in(2)) {
    return Multiplication(n->in(1), 2);
  }

  return make_invalid();
}

// Try to match `n = a << CON`. On success, return a struct with `.valid = true`, `variable = a`, and
// `multiplier = 1 << CON`.
// Match `n` for pattern: a << CON.
// Note that the power-of-2 multiplication optimization could potentially convert a MulNode to this pattern.
AddNode::Multiplication AddNode::Multiplication::find_simple_lshift_pattern(const Node* n, BasicType bt) {
  // Note that power-of-2 multiplication optimization could potentially convert a MulNode to this pattern
  if (n->Opcode() == Op_LShift(bt) && n->in(2)->is_Con()) {
    Node* con = n->in(2);
    if (!con->is_top()) {
      return Multiplication(n->in(1), java_shift_left(1, con->get_int(), bt));
    }
  }

  return make_invalid();
}

// Try to match `n = CON * a`. On success, return a struct with `.valid = true`, `variable = a`, and `multiplier = CON`.
// Match `n` for patterns: CON * a
// Note that `CON` will always be the second input node of a Mul node canonicalized by Ideal(). If this is not the case,
// `n` has not been processed by iGVN. So we skip the optimization for the current add node and wait for to be added to
// the queue again.
AddNode::Multiplication AddNode::Multiplication::find_simple_multiplication_pattern(const Node* n, BasicType bt) {
  if (n->Opcode() == Op_Mul(bt) && n->in(2)->is_Con()) {
    Node* con = n->in(2);
    Node* base = n->in(1);

    if (!con->is_top()) {
      return Multiplication(base, con->get_integer_as_long(bt));
    }
  }

  return make_invalid();
}

// Try to match `n = (a << CON1) + (a << CON2)`. On success, return a struct with `.valid = true`, `variable = a`, and
// `multiplier = (1 << CON1) + (1 << CON2)`.
// Match `n` for patterns:
//     - (1) (a << CON) + (a << CON)
//     - (2) (a << CON) + a
//     - (3) a + (a << CON)
//     - (4) a + a
// Note that one or both of the term of the addition could simply be `a` (i.e., a << 0) as in pattern (4).
AddNode::Multiplication AddNode::Multiplication::find_power_of_two_addition_pattern(const Node* n, BasicType bt) {
  if (n->Opcode() == Op_Add(bt) && n->in(1) != n->in(2)) {
    const Multiplication lhs = find_simple_lshift_pattern(n->in(1), bt);
    const Multiplication rhs = find_simple_lshift_pattern(n->in(2), bt);

    // Pattern (1)
    {
      const Multiplication res = lhs.add(rhs);
      if (res.is_valid()) {
        return res;
      }
    }

    // Pattern (2)
    if (lhs.is_valid_with(n->in(2))) {
      return Multiplication(lhs.variable(), java_add(lhs.multiplier(), CONST64(1)));
    }

    // Pattern (3)
    if (rhs.is_valid_with(n->in(1))) {
      return Multiplication(rhs.variable(), java_add(rhs.multiplier(), CONST64(1)));
    }

    // Pattern (4), which is equivalent to a simple addition pattern
    return find_simple_addition_pattern(n, bt);
  }

  return make_invalid();
}

Node* AddINode::Ideal(PhaseGVN* phase, bool can_reshape) {
  Node* in1 = in(1);
  Node* in2 = in(2);
  int op1 = in1->Opcode();
  int op2 = in2->Opcode();

  // Convert (x>>>z)+y into (x+(y<<z))>>>z for small constant z and y.
  // Helps with array allocation math constant folding
  // See 4790063:
  // Unrestricted transformation is unsafe for some runtime values of 'x'
  // ( x ==  0, z == 1, y == -1 ) fails
  // ( x == -5, z == 1, y ==  1 ) fails
  // Transform works for small z and small negative y when the addition
  // (x + (y << z)) does not cross zero.
  // Implement support for negative y and (x >= -(y << z))
  // Have not observed cases where type information exists to support
  // positive y and (x <= -(y << z))
  if (op1 == Op_URShiftI && op2 == Op_ConI &&
      in1->in(2)->Opcode() == Op_ConI) {
    jint z = phase->type(in1->in(2))->is_int()->get_con() & 0x1f; // only least significant 5 bits matter
    jint y = phase->type(in2)->is_int()->get_con();

    if (z < 5 && -5 < y && y < 0) {
      const Type* t_in11 = phase->type(in1->in(1));
      if( t_in11 != Type::TOP && (t_in11->is_int()->_lo >= -(y << z))) {
        Node* a = phase->transform(new AddINode( in1->in(1), phase->intcon(y<<z)));
        return new URShiftINode(a, in1->in(2));
      }
    }
  }

  return AddNode::IdealIL(phase, can_reshape, T_INT);
}


//------------------------------Identity---------------------------------------
// Fold (x-y)+y  OR  y+(x-y)  into  x
Node* AddINode::Identity(PhaseGVN* phase) {
  if (in(1)->Opcode() == Op_SubI && in(1)->in(2) == in(2)) {
    return in(1)->in(1);
  } else if (in(2)->Opcode() == Op_SubI && in(2)->in(2) == in(1)) {
    return in(2)->in(1);
  }
  return AddNode::Identity(phase);
}


//------------------------------add_ring---------------------------------------
// Supplied function returns the sum of the inputs.  Guaranteed never
// to be passed a TOP or BOTTOM type, these are filtered out by
// pre-check.
const Type *AddINode::add_ring( const Type *t0, const Type *t1 ) const {
  const TypeInt *r0 = t0->is_int(); // Handy access
  const TypeInt *r1 = t1->is_int();
  int lo = java_add(r0->_lo, r1->_lo);
  int hi = java_add(r0->_hi, r1->_hi);
  if( !(r0->is_con() && r1->is_con()) ) {
    // Not both constants, compute approximate result
    if( (r0->_lo & r1->_lo) < 0 && lo >= 0 ) {
      lo = min_jint; hi = max_jint; // Underflow on the low side
    }
    if( (~(r0->_hi | r1->_hi)) < 0 && hi < 0 ) {
      lo = min_jint; hi = max_jint; // Overflow on the high side
    }
    if( lo > hi ) {               // Handle overflow
      lo = min_jint; hi = max_jint;
    }
  } else {
    // both constants, compute precise result using 'lo' and 'hi'
    // Semantics define overflow and underflow for integer addition
    // as expected.  In particular: 0x80000000 + 0x80000000 --> 0x0
  }
  return TypeInt::make( lo, hi, MAX2(r0->_widen,r1->_widen) );
}


//=============================================================================
//------------------------------Idealize---------------------------------------
Node* AddLNode::Ideal(PhaseGVN* phase, bool can_reshape) {
  return AddNode::IdealIL(phase, can_reshape, T_LONG);
}


//------------------------------Identity---------------------------------------
// Fold (x-y)+y  OR  y+(x-y)  into  x
Node* AddLNode::Identity(PhaseGVN* phase) {
  if (in(1)->Opcode() == Op_SubL && in(1)->in(2) == in(2)) {
    return in(1)->in(1);
  } else if (in(2)->Opcode() == Op_SubL && in(2)->in(2) == in(1)) {
    return in(2)->in(1);
  }
  return AddNode::Identity(phase);
}


//------------------------------add_ring---------------------------------------
// Supplied function returns the sum of the inputs.  Guaranteed never
// to be passed a TOP or BOTTOM type, these are filtered out by
// pre-check.
const Type *AddLNode::add_ring( const Type *t0, const Type *t1 ) const {
  const TypeLong *r0 = t0->is_long(); // Handy access
  const TypeLong *r1 = t1->is_long();
  jlong lo = java_add(r0->_lo, r1->_lo);
  jlong hi = java_add(r0->_hi, r1->_hi);
  if( !(r0->is_con() && r1->is_con()) ) {
    // Not both constants, compute approximate result
    if( (r0->_lo & r1->_lo) < 0 && lo >= 0 ) {
      lo =min_jlong; hi = max_jlong; // Underflow on the low side
    }
    if( (~(r0->_hi | r1->_hi)) < 0 && hi < 0 ) {
      lo = min_jlong; hi = max_jlong; // Overflow on the high side
    }
    if( lo > hi ) {               // Handle overflow
      lo = min_jlong; hi = max_jlong;
    }
  } else {
    // both constants, compute precise result using 'lo' and 'hi'
    // Semantics define overflow and underflow for integer addition
    // as expected.  In particular: 0x80000000 + 0x80000000 --> 0x0
  }
  return TypeLong::make( lo, hi, MAX2(r0->_widen,r1->_widen) );
}


//=============================================================================
//------------------------------Ideal------------------------------------------
Node* AddFPNode::Ideal(PhaseGVN* phase, bool can_reshape) {
  // Floating-point addition is commutative but not associative.
  return commute(phase, this) ? this : nullptr;
}

//=============================================================================
//------------------------------add_of_identity--------------------------------
// Check for addition of the identity
const Type *AddFNode::add_of_identity( const Type *t1, const Type *t2 ) const {
  // x ADD 0  should return x unless 'x' is a -zero
  //
  // const Type *zero = add_id();     // The additive identity
  // jfloat f1 = t1->getf();
  // jfloat f2 = t2->getf();
  //
  // if( t1->higher_equal( zero ) ) return t2;
  // if( t2->higher_equal( zero ) ) return t1;

  return nullptr;
}

//------------------------------add_ring---------------------------------------
// Supplied function returns the sum of the inputs.
// This also type-checks the inputs for sanity.  Guaranteed never to
// be passed a TOP or BOTTOM type, these are filtered out by pre-check.
const Type *AddFNode::add_ring( const Type *t0, const Type *t1 ) const {
  if (!t0->isa_float_constant() || !t1->isa_float_constant()) {
    return bottom_type();
  }
  return TypeF::make( t0->getf() + t1->getf() );
}

//=============================================================================
//------------------------------add_of_identity--------------------------------
// Check for addition of the identity
const Type* AddHFNode::add_of_identity(const Type* t1, const Type* t2) const {
  return nullptr;
}

// Supplied function returns the sum of the inputs.
// This also type-checks the inputs for sanity.  Guaranteed never to
// be passed a TOP or BOTTOM type, these are filtered out by pre-check.
const Type* AddHFNode::add_ring(const Type* t0, const Type* t1) const {
  if (!t0->isa_half_float_constant() || !t1->isa_half_float_constant()) {
    return bottom_type();
  }
  return TypeH::make(t0->getf() + t1->getf());
}

//=============================================================================
//------------------------------add_of_identity--------------------------------
// Check for addition of the identity
const Type *AddDNode::add_of_identity( const Type *t1, const Type *t2 ) const {
  // x ADD 0  should return x unless 'x' is a -zero
  //
  // const Type *zero = add_id();     // The additive identity
  // jfloat f1 = t1->getf();
  // jfloat f2 = t2->getf();
  //
  // if( t1->higher_equal( zero ) ) return t2;
  // if( t2->higher_equal( zero ) ) return t1;

  return nullptr;
}
//------------------------------add_ring---------------------------------------
// Supplied function returns the sum of the inputs.
// This also type-checks the inputs for sanity.  Guaranteed never to
// be passed a TOP or BOTTOM type, these are filtered out by pre-check.
const Type *AddDNode::add_ring( const Type *t0, const Type *t1 ) const {
  if (!t0->isa_double_constant() || !t1->isa_double_constant()) {
    return bottom_type();
  }
  return TypeD::make( t0->getd() + t1->getd() );
}


//=============================================================================
//------------------------------Identity---------------------------------------
// If one input is a constant 0, return the other input.
Node* AddPNode::Identity(PhaseGVN* phase) {
  return ( phase->type( in(Offset) )->higher_equal( TypeX_ZERO ) ) ? in(Address) : this;
}

//------------------------------Idealize---------------------------------------
Node *AddPNode::Ideal(PhaseGVN *phase, bool can_reshape) {
  // Bail out if dead inputs
  if( phase->type( in(Address) ) == Type::TOP ) return nullptr;

  // If the left input is an add of a constant, flatten the expression tree.
  const Node *n = in(Address);
  if (n->is_AddP() && n->in(Base) == in(Base)) {
    const AddPNode *addp = n->as_AddP(); // Left input is an AddP
    assert( !addp->in(Address)->is_AddP() ||
             addp->in(Address)->as_AddP() != addp,
            "dead loop in AddPNode::Ideal" );
    // Type of left input's right input
    const Type *t = phase->type( addp->in(Offset) );
    if( t == Type::TOP ) return nullptr;
    const TypeX *t12 = t->is_intptr_t();
    if( t12->is_con() ) {       // Left input is an add of a constant?
      // If the right input is a constant, combine constants
      const Type *temp_t2 = phase->type( in(Offset) );
      if( temp_t2 == Type::TOP ) return nullptr;
      const TypeX *t2 = temp_t2->is_intptr_t();
      Node* address;
      Node* offset;
      if( t2->is_con() ) {
        // The Add of the flattened expression
        address = addp->in(Address);
        offset  = phase->MakeConX(t2->get_con() + t12->get_con());
      } else {
        // Else move the constant to the right.  ((A+con)+B) into ((A+B)+con)
        address = phase->transform(AddPNode::make_with_base(in(Base), addp->in(Address), in(Offset)));
        offset  = addp->in(Offset);
      }
      set_req_X(Address, address, phase);
      set_req_X(Offset, offset, phase);
      return this;
    }
  }

  // Raw pointers?
  if( in(Base)->bottom_type() == Type::TOP ) {
    // If this is a null+long form (from unsafe accesses), switch to a rawptr.
    if (phase->type(in(Address)) == TypePtr::NULL_PTR) {
      Node* offset = in(Offset);
      return new CastX2PNode(offset);
    }
  }

  // If the right is an add of a constant, push the offset down.
  // Convert: (ptr + (offset+con)) into (ptr+offset)+con.
  // The idea is to merge array_base+scaled_index groups together,
  // and only have different constant offsets from the same base.
  const Node* add = in(Offset);
  if (add->Opcode() == Op_AddX && add->in(1) != add) {
    const Type* t22 = phase->type(add->in(2));
    if (t22->singleton() && (t22 != Type::TOP)) {  // Right input is an add of a constant?
      set_req(Address, phase->transform(AddPNode::make_with_base(in(Base), in(Address), add->in(1))));
      set_req_X(Offset, add->in(2), phase); // puts add on igvn worklist if needed
      return this;              // Made progress
    }
  }

  return nullptr;                  // No progress
}

//------------------------------bottom_type------------------------------------
// Bottom-type is the pointer-type with unknown offset.
const Type *AddPNode::bottom_type() const {
  if (in(Address) == nullptr)  return TypePtr::BOTTOM;
  const TypePtr *tp = in(Address)->bottom_type()->isa_ptr();
  if( !tp ) return Type::TOP;   // TOP input means TOP output

  assert(in(Offset)->Opcode() != Op_ConP, "");
  const Type* t = in(Offset)->bottom_type();
  if (t == Type::TOP) {
    return Type::TOP;
  }

  const TypeX* tx = t->is_intptr_t();
  intptr_t txoffset = Type::OffsetBot;
  if (tx->is_con()) {   // Left input is an add of a constant?
    txoffset = tx->get_con();
  }
  if (tp->isa_aryptr()) {
    // In the case of a flat inline type array, each field has its
    // own slice so we need to extract the field being accessed from
    // the address computation
    return tp->is_aryptr()->add_field_offset_and_offset(txoffset);
  }
  return tp->add_offset(txoffset);
}

//------------------------------Value------------------------------------------
const Type* AddPNode::Value(PhaseGVN* phase) const {
  // Either input is TOP ==> the result is TOP
  const Type *t1 = phase->type( in(Address) );
  const Type *t2 = phase->type( in(Offset) );
  if( t1 == Type::TOP ) return Type::TOP;
  if( t2 == Type::TOP ) return Type::TOP;

  // Left input is a pointer
  const TypePtr *p1 = t1->isa_ptr();
  // Right input is an int
  const TypeX *p2 = t2->is_intptr_t();
  // Add 'em
  intptr_t p2offset = Type::OffsetBot;
  if (p2->is_con()) {   // Left input is an add of a constant?
    p2offset = p2->get_con();
  }
  if (p1->isa_aryptr()) {
    // In the case of a flat inline type array, each field has its
    // own slice so we need to extract the field being accessed from
    // the address computation
    return p1->is_aryptr()->add_field_offset_and_offset(p2offset);
  }
  return p1->add_offset(p2offset);
}

//------------------------Ideal_base_and_offset--------------------------------
// Split an oop pointer into a base and offset.
// (The offset might be Type::OffsetBot in the case of an array.)
// Return the base, or null if failure.
Node* AddPNode::Ideal_base_and_offset(Node* ptr, PhaseValues* phase,
                                      // second return value:
                                      intptr_t& offset) {
  if (ptr->is_AddP()) {
    Node* base = ptr->in(AddPNode::Base);
    Node* addr = ptr->in(AddPNode::Address);
    Node* offs = ptr->in(AddPNode::Offset);
    if (base == addr || base->is_top()) {
      offset = phase->find_intptr_t_con(offs, Type::OffsetBot);
      if (offset != Type::OffsetBot) {
        return addr;
      }
    }
  }
  offset = Type::OffsetBot;
  return nullptr;
}

//------------------------------unpack_offsets----------------------------------
// Collect the AddP offset values into the elements array, giving up
// if there are more than length.
int AddPNode::unpack_offsets(Node* elements[], int length) const {
  int count = 0;
  Node const* addr = this;
  Node* base = addr->in(AddPNode::Base);
  while (addr->is_AddP()) {
    if (addr->in(AddPNode::Base) != base) {
      // give up
      return -1;
    }
    elements[count++] = addr->in(AddPNode::Offset);
    if (count == length) {
      // give up
      return -1;
    }
    addr = addr->in(AddPNode::Address);
  }
  if (addr != base) {
    return -1;
  }
  return count;
}

//------------------------------match_edge-------------------------------------
// Do we Match on this edge index or not?  Do not match base pointer edge
uint AddPNode::match_edge(uint idx) const {
  return idx > Base;
}

//=============================================================================
//------------------------------Identity---------------------------------------
Node* OrINode::Identity(PhaseGVN* phase) {
  // x | x => x
  if (in(1) == in(2)) {
    return in(1);
  }

  return AddNode::Identity(phase);
}

// Find shift value for Integer or Long OR.
static Node* rotate_shift(PhaseGVN* phase, Node* lshift, Node* rshift, int mask) {
  // val << norm_con_shift | val >> ({32|64} - norm_con_shift) => rotate_left val, norm_con_shift
  const TypeInt* lshift_t = phase->type(lshift)->isa_int();
  const TypeInt* rshift_t = phase->type(rshift)->isa_int();
  if (lshift_t != nullptr && lshift_t->is_con() &&
      rshift_t != nullptr && rshift_t->is_con() &&
      ((lshift_t->get_con() & mask) == ((mask + 1) - (rshift_t->get_con() & mask)))) {
    return phase->intcon(lshift_t->get_con() & mask);
  }
  // val << var_shift | val >> ({0|32|64} - var_shift) => rotate_left val, var_shift
  if (rshift->Opcode() == Op_SubI && rshift->in(2) == lshift && rshift->in(1)->is_Con()){
    const TypeInt* shift_t = phase->type(rshift->in(1))->isa_int();
    if (shift_t != nullptr && shift_t->is_con() &&
        (shift_t->get_con() == 0 || shift_t->get_con() == (mask + 1))) {
      return lshift;
    }
  }
  return nullptr;
}

Node* OrINode::Ideal(PhaseGVN* phase, bool can_reshape) {
  int lopcode = in(1)->Opcode();
  int ropcode = in(2)->Opcode();
  if (Matcher::match_rule_supported(Op_RotateLeft) &&
      lopcode == Op_LShiftI && ropcode == Op_URShiftI && in(1)->in(1) == in(2)->in(1)) {
    Node* lshift = in(1)->in(2);
    Node* rshift = in(2)->in(2);
    Node* shift = rotate_shift(phase, lshift, rshift, 0x1F);
    if (shift != nullptr) {
      return new RotateLeftNode(in(1)->in(1), shift, TypeInt::INT);
    }
    return nullptr;
  }
  if (Matcher::match_rule_supported(Op_RotateRight) &&
      lopcode == Op_URShiftI && ropcode == Op_LShiftI && in(1)->in(1) == in(2)->in(1)) {
    Node* rshift = in(1)->in(2);
    Node* lshift = in(2)->in(2);
    Node* shift = rotate_shift(phase, rshift, lshift, 0x1F);
    if (shift != nullptr) {
      return new RotateRightNode(in(1)->in(1), shift, TypeInt::INT);
    }
  }

  // Convert "~a | ~b" into "~(a & b)"
  if (AddNode::is_not(phase, in(1), T_INT) && AddNode::is_not(phase, in(2), T_INT)) {
    Node* and_a_b = new AndINode(in(1)->in(1), in(2)->in(1));
    Node* tn = phase->transform(and_a_b);
    return AddNode::make_not(phase, tn, T_INT);
  }
  return AddNode::Ideal(phase, can_reshape);
}

//------------------------------add_ring---------------------------------------
// Supplied function returns the sum of the inputs IN THE CURRENT RING.  For
// the logical operations the ring's ADD is really a logical OR function.
// This also type-checks the inputs for sanity.  Guaranteed never to
// be passed a TOP or BOTTOM type, these are filtered out by pre-check.
const Type* OrINode::add_ring(const Type* t1, const Type* t2) const {
  return RangeInference::infer_or(t1->is_int(), t2->is_int());
}

//=============================================================================
//------------------------------Identity---------------------------------------
Node* OrLNode::Identity(PhaseGVN* phase) {
  // x | x => x
  if (in(1) == in(2)) {
    return in(1);
  }

  return AddNode::Identity(phase);
}

Node* OrLNode::Ideal(PhaseGVN* phase, bool can_reshape) {
  int lopcode = in(1)->Opcode();
  int ropcode = in(2)->Opcode();
  if (Matcher::match_rule_supported(Op_RotateLeft) &&
      lopcode == Op_LShiftL && ropcode == Op_URShiftL && in(1)->in(1) == in(2)->in(1)) {
    Node* lshift = in(1)->in(2);
    Node* rshift = in(2)->in(2);
    Node* shift = rotate_shift(phase, lshift, rshift, 0x3F);
    if (shift != nullptr) {
      return new RotateLeftNode(in(1)->in(1), shift, TypeLong::LONG);
    }
    return nullptr;
  }
  if (Matcher::match_rule_supported(Op_RotateRight) &&
      lopcode == Op_URShiftL && ropcode == Op_LShiftL && in(1)->in(1) == in(2)->in(1)) {
    Node* rshift = in(1)->in(2);
    Node* lshift = in(2)->in(2);
    Node* shift = rotate_shift(phase, rshift, lshift, 0x3F);
    if (shift != nullptr) {
      return new RotateRightNode(in(1)->in(1), shift, TypeLong::LONG);
    }
  }

  // Convert "~a | ~b" into "~(a & b)"
  if (AddNode::is_not(phase, in(1), T_LONG) && AddNode::is_not(phase, in(2), T_LONG)) {
    Node* and_a_b = new AndLNode(in(1)->in(1), in(2)->in(1));
    Node* tn = phase->transform(and_a_b);
    return AddNode::make_not(phase, tn, T_LONG);
  }

  return AddNode::Ideal(phase, can_reshape);
}

//------------------------------add_ring---------------------------------------
const Type* OrLNode::add_ring(const Type* t1, const Type* t2) const {
  return RangeInference::infer_or(t1->is_long(), t2->is_long());
}

//---------------------------Helper -------------------------------------------
/* Decide if the given node is used only in arithmetic expressions(add or sub).
 */
static bool is_used_in_only_arithmetic(Node* n, BasicType bt) {
  for (DUIterator_Fast imax, i = n->fast_outs(imax); i < imax; i++) {
    Node* u = n->fast_out(i);
    if (u->Opcode() != Op_Add(bt) && u->Opcode() != Op_Sub(bt)) {
      return false;
    }
  }
  return true;
}

//=============================================================================
//------------------------------Idealize---------------------------------------
Node* XorINode::Ideal(PhaseGVN* phase, bool can_reshape) {
  Node* in1 = in(1);
  Node* in2 = in(2);

  // Convert ~x into -1-x when ~x is used in an arithmetic expression
  // or x itself is an expression.
  if (phase->type(in2) == TypeInt::MINUS_1) { // follows LHS^(-1), i.e., ~LHS
    if (phase->is_IterGVN()) {
      if (is_used_in_only_arithmetic(this, T_INT)
          // LHS is arithmetic
          || (in1->Opcode() == Op_AddI || in1->Opcode() == Op_SubI)) {
        return new SubINode(in2, in1);
      }
    } else {
      // graph could be incomplete in GVN so we postpone to IGVN
      phase->record_for_igvn(this);
    }
  }

  // Propagate xor through constant cmoves. This pattern can occur after expansion of Conv2B nodes.
  const TypeInt* in2_type = phase->type(in2)->isa_int();
  if (in1->Opcode() == Op_CMoveI && in2_type != nullptr && in2_type->is_con()) {
    int in2_val = in2_type->get_con();

    // Get types of both sides of the CMove
    const TypeInt* left = phase->type(in1->in(CMoveNode::IfFalse))->isa_int();
    const TypeInt* right = phase->type(in1->in(CMoveNode::IfTrue))->isa_int();

    // Ensure that both sides are int constants
    if (left != nullptr && right != nullptr && left->is_con() && right->is_con()) {
      Node* cond = in1->in(CMoveNode::Condition);

      // Check that the comparison is a bool and that the cmp node type is correct
      if (cond->is_Bool()) {
        int cmp_op = cond->in(1)->Opcode();

        if (cmp_op == Op_CmpI || cmp_op == Op_CmpP) {
          int l_val = left->get_con();
          int r_val = right->get_con();

          return new CMoveINode(cond, phase->intcon(l_val ^ in2_val), phase->intcon(r_val ^ in2_val), TypeInt::INT);
        }
      }
    }
  }

  return AddNode::Ideal(phase, can_reshape);
}

const Type* XorINode::Value(PhaseGVN* phase) const {
  Node* in1 = in(1);
  Node* in2 = in(2);
  const Type* t1 = phase->type(in1);
  const Type* t2 = phase->type(in2);
  if (t1 == Type::TOP || t2 == Type::TOP) {
    return Type::TOP;
  }
  // x ^ x ==> 0
  if (in1->eqv_uncast(in2)) {
    return add_id();
  }
  return AddNode::Value(phase);
}

//------------------------------add_ring---------------------------------------
// Supplied function returns the sum of the inputs IN THE CURRENT RING.  For
// the logical operations the ring's ADD is really a logical OR function.
// This also type-checks the inputs for sanity.  Guaranteed never to
// be passed a TOP or BOTTOM type, these are filtered out by pre-check.
const Type* XorINode::add_ring(const Type* t1, const Type* t2) const {
  return RangeInference::infer_xor(t1->is_int(), t2->is_int());
}

//=============================================================================
//------------------------------add_ring---------------------------------------
const Type* XorLNode::add_ring(const Type* t1, const Type* t2) const {
  return RangeInference::infer_xor(t1->is_long(), t2->is_long());
}

Node* XorLNode::Ideal(PhaseGVN* phase, bool can_reshape) {
  Node* in1 = in(1);
  Node* in2 = in(2);

  // Convert ~x into -1-x when ~x is used in an arithmetic expression
  // or x itself is an arithmetic expression.
  if (phase->type(in2) == TypeLong::MINUS_1) { // follows LHS^(-1), i.e., ~LHS
    if (phase->is_IterGVN()) {
      if (is_used_in_only_arithmetic(this, T_LONG)
          // LHS is arithmetic
          || (in1->Opcode() == Op_AddL || in1->Opcode() == Op_SubL)) {
        return new SubLNode(in2, in1);
      }
    } else {
      // graph could be incomplete in GVN so we postpone to IGVN
      phase->record_for_igvn(this);
    }
  }
  return AddNode::Ideal(phase, can_reshape);
}

const Type* XorLNode::Value(PhaseGVN* phase) const {
  Node* in1 = in(1);
  Node* in2 = in(2);
  const Type* t1 = phase->type(in1);
  const Type* t2 = phase->type(in2);
  if (t1 == Type::TOP || t2 == Type::TOP) {
    return Type::TOP;
  }
  // x ^ x ==> 0
  if (in1->eqv_uncast(in2)) {
    return add_id();
  }

  return AddNode::Value(phase);
}

Node* MinMaxNode::build_min_max_int(Node* a, Node* b, bool is_max) {
  if (is_max) {
    return new MaxINode(a, b);
  } else {
    return new MinINode(a, b);
  }
}

Node* MinMaxNode::build_min_max_long(PhaseGVN* phase, Node* a, Node* b, bool is_max) {
  if (is_max) {
    return new MaxLNode(phase->C, a, b);
  } else {
    return new MinLNode(phase->C, a, b);
  }
}

Node* MinMaxNode::build_min_max(Node* a, Node* b, bool is_max, bool is_unsigned, const Type* t, PhaseGVN& gvn) {
  bool is_int = gvn.type(a)->isa_int();
  assert(is_int || gvn.type(a)->isa_long(), "int or long inputs");
  assert(is_int == (gvn.type(b)->isa_int() != nullptr), "inconsistent inputs");
  BasicType bt = is_int ? T_INT: T_LONG;
  Node* hook = nullptr;
  if (gvn.is_IterGVN()) {
    // Make sure a and b are not destroyed
    hook = new Node(2);
    hook->init_req(0, a);
    hook->init_req(1, b);
  }
  Node* res = nullptr;
  if (is_int && !is_unsigned) {
    res = gvn.transform(build_min_max_int(a, b, is_max));
    assert(gvn.type(res)->is_int()->_lo >= t->is_int()->_lo && gvn.type(res)->is_int()->_hi <= t->is_int()->_hi, "type doesn't match");
  } else {
    Node* cmp = nullptr;
    if (is_max) {
      cmp = gvn.transform(CmpNode::make(a, b, bt, is_unsigned));
    } else {
      cmp = gvn.transform(CmpNode::make(b, a, bt, is_unsigned));
    }
    Node* bol = gvn.transform(new BoolNode(cmp, BoolTest::lt));
    res = gvn.transform(CMoveNode::make(bol, a, b, t));
  }
  if (hook != nullptr) {
    hook->destruct(&gvn);
  }
  return res;
}

Node* MinMaxNode::build_min_max_diff_with_zero(Node* a, Node* b, bool is_max, const Type* t, PhaseGVN& gvn) {
  bool is_int = gvn.type(a)->isa_int();
  assert(is_int || gvn.type(a)->isa_long(), "int or long inputs");
  assert(is_int == (gvn.type(b)->isa_int() != nullptr), "inconsistent inputs");
  BasicType bt = is_int ? T_INT: T_LONG;
  Node* zero = gvn.integercon(0, bt);
  Node* hook = nullptr;
  if (gvn.is_IterGVN()) {
    // Make sure a and b are not destroyed
    hook = new Node(2);
    hook->init_req(0, a);
    hook->init_req(1, b);
  }
  Node* cmp = nullptr;
  if (is_max) {
    cmp = gvn.transform(CmpNode::make(a, b, bt, false));
  } else {
    cmp = gvn.transform(CmpNode::make(b, a, bt, false));
  }
  Node* sub = gvn.transform(SubNode::make(a, b, bt));
  Node* bol = gvn.transform(new BoolNode(cmp, BoolTest::lt));
  Node* res = gvn.transform(CMoveNode::make(bol, sub, zero, t));
  if (hook != nullptr) {
    hook->destruct(&gvn);
  }
  return res;
}

// Check if addition of an integer with type 't' and a constant 'c' can overflow.
static bool can_overflow(const TypeInt* t, jint c) {
  jint t_lo = t->_lo;
  jint t_hi = t->_hi;
  return ((c < 0 && (java_add(t_lo, c) > t_lo)) ||
          (c > 0 && (java_add(t_hi, c) < t_hi)));
}

// Check if addition of a long with type 't' and a constant 'c' can overflow.
static bool can_overflow(const TypeLong* t, jlong c) {
  jlong t_lo = t->_lo;
  jlong t_hi = t->_hi;
  return ((c < 0 && (java_add(t_lo, c) > t_lo)) ||
          (c > 0 && (java_add(t_hi, c) < t_hi)));
}

// Let <x, x_off> = x_operands and <y, y_off> = y_operands.
// If x == y and neither add(x, x_off) nor add(y, y_off) overflow, return
// add(x, op(x_off, y_off)). Otherwise, return nullptr.
Node* MinMaxNode::extract_add(PhaseGVN* phase, ConstAddOperands x_operands, ConstAddOperands y_operands) {
  Node* x = x_operands.first;
  Node* y = y_operands.first;
  int opcode = Opcode();
  assert(opcode == Op_MaxI || opcode == Op_MinI, "Unexpected opcode");
  const TypeInt* tx = phase->type(x)->isa_int();
  jint x_off = x_operands.second;
  jint y_off = y_operands.second;
  if (x == y && tx != nullptr &&
      !can_overflow(tx, x_off) &&
      !can_overflow(tx, y_off)) {
    jint c = opcode == Op_MinI ? MIN2(x_off, y_off) : MAX2(x_off, y_off);
    return new AddINode(x, phase->intcon(c));
  }
  return nullptr;
}

// Try to cast n as an integer addition with a constant. Return:
//   <x, C>,       if n == add(x, C), where 'C' is a non-TOP constant;
//   <nullptr, 0>, if n == add(x, C), where 'C' is a TOP constant; or
//   <n, 0>,       otherwise.
static ConstAddOperands as_add_with_constant(Node* n) {
  if (n->Opcode() != Op_AddI) {
    return ConstAddOperands(n, 0);
  }
  Node* x = n->in(1);
  Node* c = n->in(2);
  if (!c->is_Con()) {
    return ConstAddOperands(n, 0);
  }
  const Type* c_type = c->bottom_type();
  if (c_type == Type::TOP) {
    return ConstAddOperands(nullptr, 0);
  }
  return ConstAddOperands(x, c_type->is_int()->get_con());
}

Node* MinMaxNode::IdealI(PhaseGVN* phase, bool can_reshape) {
  Node* n = AddNode::Ideal(phase, can_reshape);
  if (n != nullptr) {
    return n;
  }
  int opcode = Opcode();
  assert(opcode == Op_MinI || opcode == Op_MaxI, "Unexpected opcode");
  // Try to transform the following pattern, in any of its four possible
  // permutations induced by op's commutativity:
  //     op(op(add(inner, inner_off), inner_other), add(outer, outer_off))
  // into
  //     op(add(inner, op(inner_off, outer_off)), inner_other),
  // where:
  //     op is either MinI or MaxI, and
  //     inner == outer, and
  //     the additions cannot overflow.
  for (uint inner_op_index = 1; inner_op_index <= 2; inner_op_index++) {
    if (in(inner_op_index)->Opcode() != opcode) {
      continue;
    }
    Node* outer_add = in(inner_op_index == 1 ? 2 : 1);
    ConstAddOperands outer_add_operands = as_add_with_constant(outer_add);
    if (outer_add_operands.first == nullptr) {
      return nullptr; // outer_add has a TOP input, no need to continue.
    }
    // One operand is a MinI/MaxI and the other is an integer addition with
    // constant. Test the operands of the inner MinI/MaxI.
    for (uint inner_add_index = 1; inner_add_index <= 2; inner_add_index++) {
      Node* inner_op = in(inner_op_index);
      Node* inner_add = inner_op->in(inner_add_index);
      ConstAddOperands inner_add_operands = as_add_with_constant(inner_add);
      if (inner_add_operands.first == nullptr) {
        return nullptr; // inner_add has a TOP input, no need to continue.
      }
      // Try to extract the inner add.
      Node* add_extracted = extract_add(phase, inner_add_operands, outer_add_operands);
      if (add_extracted == nullptr) {
        continue;
      }
      Node* add_transformed = phase->transform(add_extracted);
      Node* inner_other = inner_op->in(inner_add_index == 1 ? 2 : 1);
      return build_min_max_int(add_transformed, inner_other, opcode == Op_MaxI);
    }
  }
  // Try to transform
  //     op(add(x, x_off), add(y, y_off))
  // into
  //     add(x, op(x_off, y_off)),
  // where:
  //     op is either MinI or MaxI, and
  //     inner == outer, and
  //     the additions cannot overflow.
  ConstAddOperands xC = as_add_with_constant(in(1));
  ConstAddOperands yC = as_add_with_constant(in(2));
  if (xC.first == nullptr || yC.first == nullptr) return nullptr;
  return extract_add(phase, xC, yC);
}

// Ideal transformations for MaxINode
Node* MaxINode::Ideal(PhaseGVN* phase, bool can_reshape) {
  return IdealI(phase, can_reshape);
}

Node* MaxINode::Identity(PhaseGVN* phase) {
  const TypeInt* t1 = phase->type(in(1))->is_int();
  const TypeInt* t2 = phase->type(in(2))->is_int();

  // Can we determine the maximum statically?
  if (t1->_lo >= t2->_hi) {
    return in(1);
  } else if (t2->_lo >= t1->_hi) {
    return in(2);
  }

  return MinMaxNode::Identity(phase);
}

//=============================================================================
//------------------------------add_ring---------------------------------------
// Supplied function returns the sum of the inputs.
const Type *MaxINode::add_ring( const Type *t0, const Type *t1 ) const {
  const TypeInt *r0 = t0->is_int(); // Handy access
  const TypeInt *r1 = t1->is_int();

  // Otherwise just MAX them bits.
  return TypeInt::make( MAX2(r0->_lo,r1->_lo), MAX2(r0->_hi,r1->_hi), MAX2(r0->_widen,r1->_widen) );
}

//=============================================================================
//------------------------------Idealize---------------------------------------
// MINs show up in range-check loop limit calculations.  Look for
// "MIN2(x+c0,MIN2(y,x+c1))".  Pick the smaller constant: "MIN2(x+c0,y)"
Node* MinINode::Ideal(PhaseGVN* phase, bool can_reshape) {
  return IdealI(phase, can_reshape);
}

Node* MinINode::Identity(PhaseGVN* phase) {
  const TypeInt* t1 = phase->type(in(1))->is_int();
  const TypeInt* t2 = phase->type(in(2))->is_int();

  // Can we determine the minimum statically?
  if (t1->_lo >= t2->_hi) {
    return in(2);
  } else if (t2->_lo >= t1->_hi) {
    return in(1);
  }

  return MinMaxNode::Identity(phase);
}

//------------------------------add_ring---------------------------------------
// Supplied function returns the sum of the inputs.
const Type *MinINode::add_ring( const Type *t0, const Type *t1 ) const {
  const TypeInt *r0 = t0->is_int(); // Handy access
  const TypeInt *r1 = t1->is_int();

  // Otherwise just MIN them bits.
  return TypeInt::make( MIN2(r0->_lo,r1->_lo), MIN2(r0->_hi,r1->_hi), MAX2(r0->_widen,r1->_widen) );
}

// Collapse the "addition with overflow-protection" pattern, and the symmetrical
// "subtraction with underflow-protection" pattern. These are created during the
// unrolling, when we have to adjust the limit by subtracting the stride, but want
// to protect against underflow: MaxL(SubL(limit, stride), min_jint).
// If we have more than one of those in a sequence:
//
//   x  con2
//   |  |
//   AddL  clamp2
//     |    |
//    Max/MinL con1
//          |  |
//          AddL  clamp1
//            |    |
//           Max/MinL (n)
//
// We want to collapse it to:
//
//   x  con1  con2
//   |    |    |
//   |   AddLNode (new_con)
//   |    |
//  AddLNode  clamp1
//        |    |
//       Max/MinL (n)
//
// Note: we assume that SubL was already replaced by an AddL, and that the stride
// has its sign flipped: SubL(limit, stride) -> AddL(limit, -stride).
//
// Proof MaxL collapsed version equivalent to original (MinL version similar):
// is_sub_con ensures that con1, con2 ∈ [min_int, 0[
//
// Original:
// - AddL2 underflow => x + con2 ∈ ]max_long - min_int, max_long], ALWAYS BAILOUT as x + con1 + con2 surely fails can_overflow (*)
// - AddL2 no underflow => x + con2 ∈ [min_long, max_long]
//   - MaxL2 clamp => min_int
//     - AddL1 underflow: NOT POSSIBLE: cannot underflow since min_int + con1 ∈ [2 * min_int, min_int] always > min_long
//     - AddL1 no underflow => min_int + con1 ∈ [2 * min_int, min_int]
//       - MaxL1 clamp => min_int (RESULT 1)
//       - MaxL1 no clamp: NOT POSSIBLE: min_int + con1 ∈ [2 * min_int, min_int] always <= min_int, so clamp always taken
//   - MaxL2 no clamp => x + con2 ∈ [min_int, max_long]
//     - AddL1 underflow: NOT POSSIBLE: cannot underflow since x + con2 + con1 ∈ [2 * min_int, max_long] always > min_long
//     - AddL1 no underflow => x + con2 + con1 ∈ [2 * min_int, max_long]
//       - MaxL1 clamp => min_int (RESULT 2)
//       - MaxL1 no clamp => x + con2 + con1 ∈ ]min_int, max_long] (RESULT 3)
//
// Collapsed:
// - AddL2 (cannot underflow) => con2 + con1 ∈ [2 * min_int, 0]
//   - AddL1 underflow: NOT POSSIBLE: would have bailed out at can_overflow (*)
//   - AddL1 no underflow => x + con2 + con1 ∈ [min_long, max_long]
//     - MaxL clamp => min_int (RESULT 1 and RESULT 2)
//     - MaxL no clamp => x + con2 + con1 ∈ ]min_int, max_long] (RESULT 3)
//
static Node* fold_subI_no_underflow_pattern(Node* n, PhaseGVN* phase) {
  assert(n->Opcode() == Op_MaxL || n->Opcode() == Op_MinL, "sanity");
  // Check that the two clamps have the correct values.
  jlong clamp = (n->Opcode() == Op_MaxL) ? min_jint : max_jint;
  auto is_clamp = [&](Node* c) {
    const TypeLong* t = phase->type(c)->isa_long();
    return t != nullptr && t->is_con() &&
           t->get_con() == clamp;
  };
  // Check that the constants are negative if MaxL, and positive if MinL.
  auto is_sub_con = [&](Node* c) {
    const TypeLong* t = phase->type(c)->isa_long();
    return t != nullptr && t->is_con() &&
           t->get_con() < max_jint && t->get_con() > min_jint &&
           (t->get_con() < 0) == (n->Opcode() == Op_MaxL);
  };
  // Verify the graph level by level:
  Node* add1   = n->in(1);
  Node* clamp1 = n->in(2);
  if (add1->Opcode() == Op_AddL && is_clamp(clamp1)) {
    Node* max2 = add1->in(1);
    Node* con1 = add1->in(2);
    if (max2->Opcode() == n->Opcode() && is_sub_con(con1)) {
      Node* add2   = max2->in(1);
      Node* clamp2 = max2->in(2);
      if (add2->Opcode() == Op_AddL && is_clamp(clamp2)) {
        Node* x    = add2->in(1);
        Node* con2 = add2->in(2);
        if (is_sub_con(con2)) {
          // The graph could be dying (i.e. x is top) in which case type(x) is not a long.
          const TypeLong* x_long = phase->type(x)->isa_long();
          // Collapsed graph not equivalent if potential over/underflow -> bailing out (*)
          if (x_long == nullptr || can_overflow(x_long, con1->get_long() + con2->get_long())) {
            return nullptr;
          }
          Node* new_con = phase->transform(new AddLNode(con1, con2));
          Node* new_sub = phase->transform(new AddLNode(x, new_con));
          n->set_req_X(1, new_sub, phase);
          return n;
        }
      }
    }
  }
  return nullptr;
}

const Type* MaxLNode::add_ring(const Type* t0, const Type* t1) const {
  const TypeLong* r0 = t0->is_long();
  const TypeLong* r1 = t1->is_long();

  return TypeLong::make(MAX2(r0->_lo, r1->_lo), MAX2(r0->_hi, r1->_hi), MAX2(r0->_widen, r1->_widen));
}

Node* MaxLNode::Identity(PhaseGVN* phase) {
  const TypeLong* t1 = phase->type(in(1))->is_long();
  const TypeLong* t2 = phase->type(in(2))->is_long();

  // Can we determine maximum statically?
  if (t1->_lo >= t2->_hi) {
    return in(1);
  } else if (t2->_lo >= t1->_hi) {
    return in(2);
  }

  return MinMaxNode::Identity(phase);
}

Node* MaxLNode::Ideal(PhaseGVN* phase, bool can_reshape) {
  Node* n = AddNode::Ideal(phase, can_reshape);
  if (n != nullptr) {
    return n;
  }
  if (can_reshape) {
    return fold_subI_no_underflow_pattern(this, phase);
  }
  return nullptr;
}

const Type* MinLNode::add_ring(const Type* t0, const Type* t1) const {
  const TypeLong* r0 = t0->is_long();
  const TypeLong* r1 = t1->is_long();

  return TypeLong::make(MIN2(r0->_lo, r1->_lo), MIN2(r0->_hi, r1->_hi), MAX2(r0->_widen, r1->_widen));
}

Node* MinLNode::Identity(PhaseGVN* phase) {
  const TypeLong* t1 = phase->type(in(1))->is_long();
  const TypeLong* t2 = phase->type(in(2))->is_long();

  // Can we determine minimum statically?
  if (t1->_lo >= t2->_hi) {
    return in(2);
  } else if (t2->_lo >= t1->_hi) {
    return in(1);
  }

  return MinMaxNode::Identity(phase);
}

Node* MinLNode::Ideal(PhaseGVN* phase, bool can_reshape) {
  Node* n = AddNode::Ideal(phase, can_reshape);
  if (n != nullptr) {
    return n;
  }
  if (can_reshape) {
    return fold_subI_no_underflow_pattern(this, phase);
  }
  return nullptr;
}

int MinMaxNode::opposite_opcode() const {
  if (Opcode() == max_opcode()) {
    return min_opcode();
  } else {
    assert(Opcode() == min_opcode(), "Caller should be either %s or %s, but is %s", NodeClassNames[max_opcode()], NodeClassNames[min_opcode()], NodeClassNames[Opcode()]);
    return max_opcode();
  }
}

// Given a redundant structure such as Max/Min(A, Max/Min(B, C)) where A == B or A == C, return the useful part of the structure.
// 'operation' is the node expected to be the inner 'Max/Min(B, C)', and 'operand' is the node expected to be the 'A' operand of the outer node.
Node* MinMaxNode::find_identity_operation(Node* operation, Node* operand) {
  if (operation->Opcode() == Opcode() || operation->Opcode() == opposite_opcode()) {
    Node* n1 = operation->in(1);
    Node* n2 = operation->in(2);

    // Given Op(A, Op(B, C)), see if either A == B or A == C is true.
    if (n1 == operand || n2 == operand) {
      // If the operations are the same return the inner operation, as Max(A, Max(A, B)) == Max(A, B).
      if (operation->Opcode() == Opcode()) {
        return operation;
      }

      // If the operations are different return the operand 'A', as Max(A, Min(A, B)) == A if the value isn't floating point.
      // With floating point values, the identity doesn't hold if B == NaN.
      const Type* type = bottom_type();
      if (type->isa_int() || type->isa_long()) {
        return operand;
      }
    }
  }

  return nullptr;
}

Node* MinMaxNode::Identity(PhaseGVN* phase) {
  if (in(1) == in(2)) {
      return in(1);
  }

  Node* identity_1 = MinMaxNode::find_identity_operation(in(2), in(1));
  if (identity_1 != nullptr) {
    return identity_1;
  }

  Node* identity_2 = MinMaxNode::find_identity_operation(in(1), in(2));
  if (identity_2 != nullptr) {
    return identity_2;
  }

  return AddNode::Identity(phase);
}

//------------------------------add_ring---------------------------------------
const Type* MinHFNode::add_ring(const Type* t0, const Type* t1) const {
  const TypeH* r0 = t0->isa_half_float_constant();
  const TypeH* r1 = t1->isa_half_float_constant();
  if (r0 == nullptr || r1 == nullptr) {
    return bottom_type();
  }

  if (r0->is_nan()) {
    return r0;
  }
  if (r1->is_nan()) {
    return r1;
  }

  float f0 = r0->getf();
  float f1 = r1->getf();
  if (f0 != 0.0f || f1 != 0.0f) {
    return f0 < f1 ? r0 : r1;
  }

  // As per IEEE 754 specification, floating point comparison consider +ve and -ve
  // zeros as equals. Thus, performing signed integral comparison for min value
  // detection.
  return (jint_cast(f0) < jint_cast(f1)) ? r0 : r1;
}

//------------------------------add_ring---------------------------------------
const Type* MinFNode::add_ring(const Type* t0, const Type* t1 ) const {
  const TypeF* r0 = t0->isa_float_constant();
  const TypeF* r1 = t1->isa_float_constant();
  if (r0 == nullptr || r1 == nullptr) {
    return bottom_type();
  }

  if (r0->is_nan()) {
    return r0;
  }
  if (r1->is_nan()) {
    return r1;
  }

  float f0 = r0->getf();
  float f1 = r1->getf();
  if (f0 != 0.0f || f1 != 0.0f) {
    return f0 < f1 ? r0 : r1;
  }

  // handle min of 0.0, -0.0 case.
  return (jint_cast(f0) < jint_cast(f1)) ? r0 : r1;
}

//------------------------------add_ring---------------------------------------
const Type* MinDNode::add_ring(const Type* t0, const Type* t1) const {
  const TypeD* r0 = t0->isa_double_constant();
  const TypeD* r1 = t1->isa_double_constant();
  if (r0 == nullptr || r1 == nullptr) {
    return bottom_type();
  }

  if (r0->is_nan()) {
    return r0;
  }
  if (r1->is_nan()) {
    return r1;
  }

  double d0 = r0->getd();
  double d1 = r1->getd();
  if (d0 != 0.0 || d1 != 0.0) {
    return d0 < d1 ? r0 : r1;
  }

  // handle min of 0.0, -0.0 case.
  return (jlong_cast(d0) < jlong_cast(d1)) ? r0 : r1;
}

//------------------------------add_ring---------------------------------------
const Type* MaxHFNode::add_ring(const Type* t0, const Type* t1) const {
  const TypeH* r0 = t0->isa_half_float_constant();
  const TypeH* r1 = t1->isa_half_float_constant();
  if (r0 == nullptr || r1 == nullptr) {
    return bottom_type();
  }

  if (r0->is_nan()) {
    return r0;
  }
  if (r1->is_nan()) {
    return r1;
  }

  float f0 = r0->getf();
  float f1 = r1->getf();
  if (f0 != 0.0f || f1 != 0.0f) {
    return f0 > f1 ? r0 : r1;
  }

  // As per IEEE 754 specification, floating point comparison consider +ve and -ve
  // zeros as equals. Thus, performing signed integral comparison for max value
  // detection.
  return (jint_cast(f0) > jint_cast(f1)) ? r0 : r1;
}


//------------------------------add_ring---------------------------------------
const Type* MaxFNode::add_ring(const Type* t0, const Type* t1) const {
  const TypeF* r0 = t0->isa_float_constant();
  const TypeF* r1 = t1->isa_float_constant();
  if (r0 == nullptr || r1 == nullptr) {
    return bottom_type();
  }

  if (r0->is_nan()) {
    return r0;
  }
  if (r1->is_nan()) {
    return r1;
  }

  float f0 = r0->getf();
  float f1 = r1->getf();
  if (f0 != 0.0f || f1 != 0.0f) {
    return f0 > f1 ? r0 : r1;
  }

  // handle max of 0.0,-0.0 case.
  return (jint_cast(f0) > jint_cast(f1)) ? r0 : r1;
}

//------------------------------add_ring---------------------------------------
const Type* MaxDNode::add_ring(const Type* t0, const Type* t1) const {
  const TypeD* r0 = t0->isa_double_constant();
  const TypeD* r1 = t1->isa_double_constant();
  if (r0 == nullptr || r1 == nullptr) {
    return bottom_type();
  }

  if (r0->is_nan()) {
    return r0;
  }
  if (r1->is_nan()) {
    return r1;
  }

  double d0 = r0->getd();
  double d1 = r1->getd();
  if (d0 != 0.0 || d1 != 0.0) {
    return d0 > d1 ? r0 : r1;
  }

  // handle max of 0.0, -0.0 case.
  return (jlong_cast(d0) > jlong_cast(d1)) ? r0 : r1;
}

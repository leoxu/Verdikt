// Models of the compiled part of libstdc++ that header-only STL code calls: the red-black tree node operations behind
// std::map/set. They are the plain binary-search-tree operations (no rebalancing: balance affects only the depth, never
// the ordering or the set of nodes). Regenerate models/libstdcxx.core with:  hlirgen models/libstdcxx.cpp -o models/libstdcxx.core
namespace std {
struct _Rb_tree_node_base {
  int _M_color;
  _Rb_tree_node_base *_M_parent, *_M_left, *_M_right;
};

static _Rb_tree_node_base *minimum(_Rb_tree_node_base *x) { while (x->_M_left) x = x->_M_left; return x; }
static _Rb_tree_node_base *maximum(_Rb_tree_node_base *x) { while (x->_M_right) x = x->_M_right; return x; }

_Rb_tree_node_base *_Rb_tree_increment(_Rb_tree_node_base *x) throw() {
  if (x->_M_right) return minimum(x->_M_right);
  _Rb_tree_node_base *y = x->_M_parent;
  while (x == y->_M_right) { x = y; y = y->_M_parent; }
  if (x->_M_right != y) x = y;
  return x;
}
const _Rb_tree_node_base *_Rb_tree_increment(const _Rb_tree_node_base *x) throw() { return _Rb_tree_increment(const_cast<_Rb_tree_node_base *>(x)); }

_Rb_tree_node_base *_Rb_tree_decrement(_Rb_tree_node_base *x) throw() {
  if (x->_M_color == 0 && x->_M_parent->_M_parent == x) return x->_M_right;  // the header: end() -> rightmost
  if (x->_M_left) return maximum(x->_M_left);
  _Rb_tree_node_base *y = x->_M_parent;
  while (x == y->_M_left) { x = y; y = y->_M_parent; }
  return y;
}
const _Rb_tree_node_base *_Rb_tree_decrement(const _Rb_tree_node_base *x) throw() { return _Rb_tree_decrement(const_cast<_Rb_tree_node_base *>(x)); }

void _Rb_tree_insert_and_rebalance(const bool insert_left, _Rb_tree_node_base *x, _Rb_tree_node_base *p, _Rb_tree_node_base &header) throw() {
  x->_M_parent = p; x->_M_left = 0; x->_M_right = 0; x->_M_color = 1;  // black: only the header is red (decrement tells it apart by that)
  if (insert_left) {
    p->_M_left = x;
    if (p == &header) { header._M_parent = x; header._M_right = x; }
    else if (p == header._M_left) header._M_left = x;
  } else {
    p->_M_right = x;
    if (p == header._M_right) header._M_right = x;
  }
}

static void replace(_Rb_tree_node_base *z, _Rb_tree_node_base *by, _Rb_tree_node_base &header) {
  _Rb_tree_node_base *p = z->_M_parent;
  if (z == header._M_parent) header._M_parent = by;
  else if (z == p->_M_left) p->_M_left = by;
  else p->_M_right = by;
  if (by) by->_M_parent = p;
}

_Rb_tree_node_base *_Rb_tree_rebalance_for_erase(_Rb_tree_node_base *z, _Rb_tree_node_base &header) throw() {
  if (!z->_M_left || !z->_M_right) {
    _Rb_tree_node_base *x = z->_M_left ? z->_M_left : z->_M_right;
    if (z == header._M_left) header._M_left = !z->_M_right ? z->_M_parent : minimum(x);
    if (z == header._M_right) header._M_right = !z->_M_left ? z->_M_parent : maximum(x);
    replace(z, x, header);
  } else {
    _Rb_tree_node_base *y = minimum(z->_M_right);
    if (y != z->_M_right) {
      y->_M_parent->_M_left = y->_M_right;
      if (y->_M_right) y->_M_right->_M_parent = y->_M_parent;
      y->_M_right = z->_M_right;
      z->_M_right->_M_parent = y;
    }
    y->_M_left = z->_M_left;
    z->_M_left->_M_parent = y;
    replace(z, y, header);
    y->_M_color = z->_M_color;
  }
  return z;
}
}  // namespace std

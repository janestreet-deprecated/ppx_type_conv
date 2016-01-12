## 113.24.00

- Kill the nonrec rewrite done by typerep. It is no longer needed since
  4.02.2, we kept it only for compatibility with the camlp4 code.

- Cleanup in type\_conv: remove `Type_conv.Generator_result.make_at_the_end`,
  which was a hack to remove warnings. We can do it better now, and because this
  is only for signatures, the code generation issue what we had in
  simplify-type-conv-ignore-unused-warning doesn't apply.

- Update to follow `Ppx_core` evolution.

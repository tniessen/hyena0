#pragma once

#include "s-expr.h"

// TODO: checking path feasibility could be much more efficient by using yices'
// push-pop or multi-checks modes instead of one-shot.
s_expr_list solve(const s_expr_list& stmts, bool ef_mode);

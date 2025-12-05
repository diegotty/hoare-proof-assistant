datatype k = I of int | B of bool;
datatype exp = K of k | X of string | Plus of (exp * exp) | Less of (exp * exp)
datatype imp = Skip | Sec of (imp * imp) | If of (bool * imp * imp) |  While of (bool * imp) | := of (string * exp);

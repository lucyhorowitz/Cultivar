# snf_server.py
# Adapted from sage_server.py in https://github.com/mkaratarakis/sagestuff
#
# Persistent Sage subprocess that dispatches JSON requests by an "op" field.
# To add a new operation: define a function and decorate it with @op("name").
# The function receives the parsed request dict and returns a dict; the
# framework handles JSON encoding and error reporting.
#
# Currently supported ops:
#   "snf"      -> {"matrix": [[...]]}         returns U, D, V, Uinv, Vinv
#   "boundary" -> {"facets": [[...]], "n":k}  returns d_k and the bases used
#   "homology" -> {"facets": [[...]], "dim"?:k, "base_ring"?:"ZZ"|"QQ"|"GF(p)",
#                  "reduced"?:bool, "witnesses"?:bool}
#                                             returns invariants per dim (or one dim);
#                                             if witnesses=true, also returns M, snf_k,
#                                             and snf_M for the chosen dim — the minimal
#                                             certificate Lean needs to verify H_k(X).
#                                             Requires base_ring="ZZ" and "dim".

import sys
import json
from sage.all import matrix, ZZ, QQ, GF, SimplicialComplex

HANDLERS = {}

def op(name):
    def register(fn):
        HANDLERS[name] = fn
        return fn
    return register

def mat_to_rows(M):
    return [[str(x) for x in row] for row in M.rows()]

def _maybe_json(x):
    return json.loads(x) if isinstance(x, str) else x

@op("snf")
def handle_snf(req):
    A = matrix(ZZ, _maybe_json(req["matrix"]))
    D, U, V = A.smith_form()
    return {
        "status": "ok",
        "D": mat_to_rows(D),
        "U": mat_to_rows(U),
        "Uinv": mat_to_rows(matrix(ZZ, U.inverse())),
        "V": mat_to_rows(V),
        "Vinv": mat_to_rows(matrix(ZZ, V.inverse())),
    }

def _boundary_matrix(facets, n):
    """Build ∂_n : C_n → C_{n-1} against lex-sorted bases.

    We compute the boundary map ourselves instead of calling Sage's
    `chain_complex().differential(n)`. Sage's differential matrix is indexed
    by an internal basis order that did NOT match `X.n_cells(k)`, so the
    matrix and bases we returned to Lean were inconsistent. Rather than
    reverse-engineer Sage's convention, we enumerate simplices in lex order
    and apply the alternating-sum face-deletion formula directly. This
    guarantees the matrix and the bases we return are built against the
    same order, and decouples us from Sage's chain-complex internals.

    Returns (d, dom, cod) where d is a Sage matrix over ZZ and dom, cod are
    the lex-sorted bases (lists of sorted vertex tuples).
    """
    X = SimplicialComplex(facets)

    # Lex-sorted bases. Each simplex is stored as a sorted tuple so its
    # vertices are canonically ordered; the outer sort gives a canonical
    # order on the collection of simplices.
    def simplices(k):
        if k < 0:
            return []
        return sorted(tuple(sorted(s)) for s in X.n_cells(k))

    dom = simplices(n)
    cod = simplices(n - 1)
    cod_index = {s: i for i, s in enumerate(cod)}

    # Build the differential against those lex-sorted bases via the
    # alternating-sum face-deletion formula: for sigma = (v_0, ..., v_k),
    #   d(sigma) = sum_i (-1)^i * (v_0, ..., v̂_i, ..., v_k).
    # For n = 0 the codomain is empty (unreduced convention: d_0 : C_0 → 0),
    # so we skip the loop and return a zero-row matrix — matching how Sage's
    # `chain_complex().differential(0)` behaves by default.
    entries = [[0] * len(dom) for _ in range(len(cod))]
    if cod:
        for j, sigma in enumerate(dom):
            for i in range(len(sigma)):
                face = sigma[:i] + sigma[i + 1:]
                entries[cod_index[face]][j] += (-1) ** i

    d = matrix(ZZ, len(cod), len(dom), entries)
    return d, dom, cod

@op("boundary")
def handle_boundary(req):
    facets = _maybe_json(req["facets"])
    n = int(req["n"])
    d, dom, cod = _boundary_matrix(facets, n)
    return {
        "status": "ok",
        "d": mat_to_rows(d),
        "domain_basis": [list(s) for s in dom],
        "codomain_basis": [list(s) for s in cod],
    }

def _parse_base_ring(name):
    if name == "ZZ":
        return ZZ
    if name == "QQ":
        return QQ
    if name.startswith("GF(") and name.endswith(")"):
        return GF(int(name[3:-1]))
    raise ValueError(f"unsupported base_ring: {name}")

def _snf_witness_block(A):
    """Return {U, Uinv, V, Vinv, D} for A.smith_form() as JSON-ready rows."""
    A = matrix(ZZ, A)
    D, U, V = A.smith_form()
    return {
        "U": mat_to_rows(U),
        "Uinv": mat_to_rows(matrix(ZZ, U.inverse())),
        "V": mat_to_rows(V),
        "Vinv": mat_to_rows(matrix(ZZ, V.inverse())),
        "D": mat_to_rows(D),
    }

@op("homology")
def handle_homology(req):
    facets = _maybe_json(req["facets"])
    base_ring_name = req.get("base_ring", "ZZ")
    base_ring = _parse_base_ring(base_ring_name)
    reduced = bool(req.get("reduced", False))
    witnesses = bool(req.get("witnesses", False))

    if witnesses:
        if base_ring_name != "ZZ":
            raise ValueError("witnesses=true requires base_ring='ZZ'")
        if "dim" not in req:
            raise ValueError("witnesses=true requires 'dim'")
        if reduced:
            raise ValueError("witnesses=true is not supported with reduced=true")

    X = SimplicialComplex(facets)
    H = X.homology(base_ring=base_ring, reduced=reduced)

    def invariants(G):
        # AdditiveAbelianGroup.invariants() returns (0, 0, ..., d1, d2, ...)
        # where 0 = free factor (a copy of ZZ) and positive entries are torsion orders.
        # Over a field, Sage returns a vector space: fall back to its dimension
        # as a list of zeros so the caller sees Betti-number-many free factors.
        if hasattr(G, "invariants"):
            return [int(x) for x in G.invariants()]
        return [0] * int(G.dimension())

    if "dim" in req:
        d = int(req["dim"])
        result = {"status": "ok", "invariants": invariants(H[d]) if d in H else []}
    else:
        result = {"status": "ok",
                  "homology": {str(d): invariants(G) for d, G in H.items()}}

    if witnesses:
        d = int(req["dim"])
        dk, _, _ = _boundary_matrix(facets, d)
        dk1, _, _ = _boundary_matrix(facets, d + 1)
        # SNF of ∂_k.
        Dk, Uk, Vk = dk.smith_form()
        # r = number of nonzero diagonal entries of Dk. Diagonal has length
        # min(rows, cols); SNF guarantees nonzero entries come first.
        r = sum(1 for i in range(min(Dk.nrows(), Dk.ncols())) if Dk[i, i] != 0)
        # n = number of k-cells = ncols(∂_k) = nrows(∂_{k+1}).
        n_cells_k = dk.ncols()
        # M = bottom (n - r) rows of V_k^{-1} · ∂_{k+1}. The cycle-coordinate
        # block; under the change of basis V_k, ker(∂_k) corresponds to the
        # last n - r basis vectors.
        Vk_inv = matrix(ZZ, Vk.inverse())
        VkInvDk1 = Vk_inv * dk1
        M = matrix(ZZ, VkInvDk1.matrix_from_rows(range(r, n_cells_k)))
        result["snf_k"] = {
            "U": mat_to_rows(Uk),
            "Uinv": mat_to_rows(matrix(ZZ, Uk.inverse())),
            "V": mat_to_rows(Vk),
            "Vinv": mat_to_rows(Vk_inv),
            "D": mat_to_rows(Dk),
        }
        result["M"] = mat_to_rows(M)
        result["snf_M"] = _snf_witness_block(M)

    return result

def process_request(line):
    try:
        req = json.loads(line)
        if "op" not in req:
            return json.dumps({"status": "error", "message": "missing required field: op"})
        name = req["op"]
        handler = HANDLERS.get(name)
        if handler is None:
            return json.dumps({"status": "error", "message": f"unknown op: {name}"})
        return json.dumps(handler(req))
    except Exception as e:
        return json.dumps({"status": "error", "message": str(e)})

# Persistent loop (unchanged from sage_server.py)
while True:
    line = sys.stdin.readline()
    if not line:
        break
    print(process_request(line), flush=True)

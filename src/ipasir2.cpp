/******************************************
Copyright (c) 2014, Tomas Balyo, Karlsruhe Institute of Technology.
Copyright (c) 2014, Armin Biere, Johannes Kepler University.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to
deal in the Software without restriction, including without limitation the
rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
IN THE SOFTWARE.
***********************************************/

/**
 * Return the name and the version of the incremental SAT
 * solving library.
 */

#include "cryptominisat.h"
#include <vector>
#include <complex>
#include <cassert>
#include <string.h>
#include "constants.h"

class SolverWrapper {
    CMSat::SATSolver* solver;

    std::vector<CMSat::Lit> assumptions;
    std::vector<CMSat::Lit> clause;

    std::vector<uint8_t> is_failed_assumption;

    enum solver_state {
        STATE_INPUT,
        STATE_SAT,
        STATE_UNSAT,
    } state;

    void createVarIfNotExists(int32_t lit) {
        if (abs(lit) > solver->nVars()) {
            solver->new_vars(abs(lit) - solver->nVars());
        }
        if (abs(lit)*2 > is_failed_assumption.size()) {
            is_failed_assumption.resize(abs(lit)*2, 0);
        }
    }

    CMSat::Lit toCMSatLit(int32_t lit) {
        return CMSat::Lit(abs(lit)-1, lit < 0);
    }

public:
    SolverWrapper() : assumptions(), clause(), state(STATE_INPUT) {
        solver = new CMSat::SATSolver;
    }

    ~SolverWrapper() {
        delete solver;
    }

    void add(int32_t lit) {
        if (state == STATE_UNSAT) {
            std::fill(is_failed_assumption.begin(), is_failed_assumption.end(), 0);
        }
        state = STATE_INPUT;
        createVarIfNotExists(lit);
        if (lit == 0) {
            solver->add_clause(clause);
            clause.clear();
        } 
        else {
            clause.push_back(toCMSatLit(lit));
        }
    }

    void assume(int32_t lit) {
        if (state == STATE_UNSAT) {
            std::fill(is_failed_assumption.begin(), is_failed_assumption.end(), 0);
        }
        state = STATE_INPUT;
        createVarIfNotExists(lit);
        assumptions.push_back(toCMSatLit(lit));
    }

    int solve() {
        CMSat::lbool ret = solver->solve(&assumptions);
        assumptions.clear();
        std::fill(is_failed_assumption.begin(), is_failed_assumption.end(), 0);

        if (ret == CMSat::l_True) {
            state = STATE_SAT;
            return 10;
        }
        else if (ret == CMSat::l_False) {
            for (CMSat::Lit failed : solver->get_conflict()) {
                is_failed_assumption[failed.toInt()] = 1;
            }
            state = STATE_UNSAT;
            return 20;
        }
        else if (ret == CMSat::l_Undef) {
            state = STATE_INPUT;
            return 0;
        }
        return -1;
    }

    int val(int32_t lit) {
        if (state != STATE_SAT) {
            return 0;
        }
        CMSat::lbool res = solver->get_model()[abs(lit)-1];
        if (res == CMSat::l_True) {
            return lit;
        }
        else if (res == CMSat::l_False) {
            return -lit;
        }
    }

    int failed(int32_t lit) {
        if (state != STATE_UNSAT) {
            return 0;
        }
        if (is_failed_assumption[toCMSatLit(-lit).toInt()]) {
            return lit;
        }
        return 0;
    }
};

extern "C" {
    #include "ipasir2.h"

    ipasir2_errorcode ipasir2_signature(const char** signature) {
        static char tmp[200];
        std::string tmp2 = "cryptominisat-";
        tmp2 += CMSat::SATSolver::get_version();
        memcpy(tmp, tmp2.c_str(), tmp2.length()+1);
        *signature = tmp;
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_init(void** solver) {
        *solver = (void*)new SolverWrapper();
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_release(void* solver) {
        delete (SolverWrapper*)solver;
        return IPASIR_E_OK;
    }

    // TODO
    ipasir2_errorcode ipasir2_options(void* solver, const char* options) {
        return IPASIR_E_UNSUPPORTED;
    }

    // TODO
    ipasir2_errorcode ipasir2_set_option(void* solver, const char* name, const char* value) {
        return IPASIR_E_UNSUPPORTED;
    }

    ipasir2_errorcode ipasir2_add(void* solver, int lit_or_zero) {
        ((SolverWrapper*)solver)->add(lit_or_zero);
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_assume(void* solver, int lit) {
        ((SolverWrapper*)solver)->assume(lit);
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_solve(void* solver, int32_t* status) {
        *status = ((SolverWrapper*)solver)->solve();
        if (*status == -1) {
            return IPASIR_E_UNKNOWN;
        }
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_val(void* solver, int32_t lit, int32_t* val) {
        *val = ((SolverWrapper*)solver)->val(lit);
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_failed(void* solver, int32_t lit, int32_t* failed) {
        *failed = ((SolverWrapper*)solver)->failed(lit);
        return IPASIR_E_OK;
    }

    // TODO
    ipasir2_errorcode ipasir2_assignment_size(void* solver, int32_t* size) {
        return IPASIR_E_UNSUPPORTED;
    }

    // TODO
    ipasir2_errorcode ipasir2_assignment(void* solver, int32_t* assignment) {
        return IPASIR_E_UNSUPPORTED;
    }

    ipasir2_errorcode ipasir2_set_terminate(void* solver, void* state, int (*terminate)(void* state)) {
        return IPASIR_E_UNSUPPORTED;
    }

    ipasir2_errorcode ipasir2_set_learn(void* solver, void* state, void (*learn)(void* state, int* clause)) {
        return IPASIR_E_UNSUPPORTED;
    }

    // TODO
    ipasir2_errorcode ipasir2_set_import_redundant_clause(void* solver, void* state, void (*import)(void* state, int32_t** clause)) {
        return IPASIR_E_UNSUPPORTED;
    }

}

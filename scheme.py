"""This module implements the core Scheme interpreter functions, including the
eval/apply mutual recurrence, environment model, and read-eval-print loop.
"""

from scheme_primitives import *
from scheme_reader import *
from ucb import main, trace

##############
# Eval/Apply #
##############

def scheme_eval(expr, env):
    """Evaluate Scheme expression EXPR in environment ENV.

    >>> expr = read_line("(+ 2 2)")
    >>> expr
    Pair('+', Pair(2, Pair(2, nil)))
    >>> scheme_eval(expr, create_global_frame())
    4
    >>> env = create_global_frame()
    >>> scheme_eval(read_line("(define (f1 a b) (+ a b))"), env)
    >>> scheme_eval(read_line("(f1 1 2)"), env)
    3
    >>> scheme_eval(read_line("(define f2 (lambda () 5))"), env)
    >>> scheme_eval(read_line("(f2)"), env)
    5
    >>> scheme_eval(read_line("(f2 2)"), env) # doctest: +IGNORE_EXCEPTION_DETAIL
    Traceback (most recent call last):
    ...
    SchemeError:
    >>> env = create_global_frame()
    >>> scheme_eval(read_line("(cond ((= 1 2)))"), env) # doctest: +IGNORE_EXCEPTION_DETAIL
    Traceback (most recent call last):
    ...
    SchemeError:
    >>> env = create_global_frame()
    >>> scheme_eval(read_line("(let ((2 2)) 2)"), env) # doctest: +IGNORE_EXCEPTION_DETAIL
    Traceback (most recent call last):
    ...
    SchemeError:
    >>> scheme_eval(read_line("(let ((x 2 3)) 2)"), env) # doctest: +IGNORE_EXCEPTION_DETAIL
    Traceback (most recent call last):
    ...
    SchemeError:
    """
    if expr is None:
        raise SchemeError("Cannot evaluate an undefined expression.")

    # Evaluate Atoms
    if scheme_symbolp(expr):
        return env.lookup(expr)
    elif scheme_atomp(expr):
        return expr

    # All non-atomic expressions are lists.
    if not scheme_listp(expr):
        raise SchemeError("malformed list: {0}".format(str(expr)))
    first, rest = expr.first, expr.second

    # Evaluate Combinations
    if first in LOGIC_FORMS:
        return scheme_eval(LOGIC_FORMS[first](rest, env), env)
    elif first == "lambda":
        return do_lambda_form(rest, env)
    elif first == "mu":
        return do_mu_form(rest)
    elif first == "define":
        return do_define_form(rest, env)
    elif first == "quote":
        return do_quote_form(rest)
    elif first == "let":
        expr, env = do_let_form(rest, env)
        return scheme_eval(expr, env)
    else:
        procedure = scheme_eval(first, env)
        args = rest.map(lambda operand: scheme_eval(operand, env))
        return scheme_apply(procedure, args, env)

def scheme_apply(procedure, args, env):
    """Apply Scheme PROCEDURE to argument values ARGS in environment ENV."""
    if isinstance(procedure, PrimitiveProcedure):
        return apply_primitive(procedure, args, env)
    
    elif isinstance(procedure, LambdaProcedure):
        if scheme_length(procedure.formals) != scheme_length(args):
            raise SchemeError("Formals amount error")
        new_frame = procedure.env.make_call_frame(procedure.formals, args)
        return scheme_eval(procedure.body, new_frame)

    elif isinstance(procedure, MuProcedure):
        if scheme_length(procedure.formals) != scheme_length(args):
            raise SchemeError("Formals amount error")
        new_frame = env.make_call_frame(procedure.formals, args)
        return scheme_eval(procedure.body, new_frame)
    else:
        raise SchemeError("Cannot call {0}".format(str(procedure)))

def apply_primitive(procedure, args, env):
    """Apply PrimitiveProcedure PROCEDURE to a Scheme list of ARGS in ENV.

    >>> env = create_global_frame()
    >>> plus = env.bindings["+"]
    >>> twos = Pair(2, Pair(2, nil))
    >>> apply_primitive(plus, twos, env)
    4
    """    
    arg_list = []
    for a in args:
        arg_list.append(a)

    if procedure.use_env == True:
        arg_list.append(env)
    try:
        return procedure.fn(*arg_list)
    except TypeError as e:
        raise SchemeError(e)

################
# Environments #
################

class Frame(object):
    """An environment frame binds Scheme symbols to Scheme values."""

    def __init__(self, parent):
        """An empty frame with a PARENT frame (that may be None)."""
        self.bindings = {}
        self.parent = parent

    def __repr__(self):
        if self.parent is None:
            return "<Global Frame>"
        else:
            s = sorted('{0}: {1}'.format(k,v) for k,v in self.bindings.items())
            return "<{{{0}}} -> {1}>".format(', '.join(s), repr(self.parent))

    def lookup(self, symbol):
        """Return the value bound to SYMBOL.  Errors if SYMBOL is not found."""
        e = self
        while e is not None:
            if symbol in e.bindings:
                return e.bindings[symbol]
            e = e.parent
        raise SchemeError("unknown identifier: {0}".format(str(symbol)))


    def global_frame(self):
        """The global environment at the root of the parent chain."""
        e = self
        while e.parent is not None:
            e = e.parent
        return e

    def make_call_frame(self, formals, vals):
        """Return a new local frame whose parent is SELF, in which the symbols
        in the Scheme formal parameter list FORMALS are bound to the Scheme
        values in the Scheme value list VALS.

        >>> env = create_global_frame()
        >>> formals, vals = read_line("(a b c)"), read_line("(1 2 3)")
        >>> env.make_call_frame(formals, vals)
        <{a: 1, b: 2, c: 3} -> <Global Frame>>

        >>> formals, vals = read_line("(a b c)"), read_line("(1 2)")
        >>> env.make_call_frame(formals, vals) # doctest: +IGNORE_EXCEPTION_DETAIL
        Traceback (most recent call last):
        ...
        SchemeError:
        
        """
        frame = Frame(self)
        while scheme_pairp(formals):
            if scheme_nullp(vals):
                raise SchemeError("Less args than needed")
            frame.define(formals.first, vals.first)
            formals = formals.second
            vals = vals.second
        if not scheme_nullp(formals):
            frame.define(formals, vals)
        elif not scheme_nullp(vals):
            raise SchemeError("More agrs than needed")
        return frame

    def define(self, sym, val):
        """Define Scheme symbol SYM to have value VAL in SELF."""
        self.bindings[sym] = val

class LambdaProcedure(object):
    """A procedure defined by a lambda expression or the complex define form."""

    def __init__(self, formals, body, env):
        """A procedure whose formal parameter list is FORMALS (a Scheme list),
        whose body is the single Scheme expression BODY, and whose parent
        environment is the Frame ENV.  A lambda expression containing multiple
        expressions, such as (lambda (x) (display x) (+ x 1)) can be handled by
        using (begin (display x) (+ x 1)) as the body."""
        self.formals = formals
        self.body = body
        self.env = env

    def __str__(self):
        return "(lambda {0} {1})".format(str(self.formals), str(self.body))

    def __repr__(self):
        args = (self.formals, self.body, self.env)
        return "LambdaProcedure({0}, {1}, {2})".format(*(repr(a) for a in args))

class MuProcedure(object):
    """A procedure defined by a mu expression, which has dynamic scope.
     _________________
    < Scheme is cool! >
     -----------------
            \   ^__^
             \  (oo)\_______
                (__)\       )\/\
                    ||----w |
                    ||     ||
    """

    def __init__(self, formals, body):
        """A procedure whose formal parameter list is FORMALS (a Scheme list),
        whose body is the single Scheme expression BODY.  A mu expression
        containing multiple expressions, such as (mu (x) (display x) (+ x 1))
        can be handled by using (begin (display x) (+ x 1)) as the body."""
        self.formals = formals
        self.body = body

    def __str__(self):
        return "(mu {0} {1})".format(str(self.formals), str(self.body))

    def __repr__(self):
        args = (self.formals, self.body)
        return "MuProcedure({0}, {1})".format(*(repr(a) for a in args))


#################
# Special forms #
#################

def do_lambda_form(vals, env):
    """Evaluate a lambda form with parameters VALS in environment ENV."""
    check_form(vals, 2)
    formals = vals[0]
    check_formals(formals)
    if len(vals.second) > 1:
        lam_body = Pair("begin", vals.second)
        return LambdaProcedure(formals, lam_body, env)
    else:
        lam_body = vals[1]
        return LambdaProcedure(formals, lam_body, env)

def do_mu_form(vals):
    """Evaluate a mu form with parameters VALS."""
    check_form(vals, 2)
    formals = vals[0]
    check_formals(formals)
    if len(vals.second) > 1:
        mu_body = Pair("begin", vals.second)
        return MuProcedure(formals, mu_body)
    else:
        mu_body = vals[1]
        return MuProcedure(formals, mu_body)


def do_define_form(vals, env):
    """Evaluate a define form with parameters VALS in environment ENV.
    #Problem5
    >>> global_frame = create_global_frame()
    >>> frame1 = Frame(global_frame)
    >>> global_frame.define('a', 1)
    >>> global_frame.define('b', 4)
    >>> frame1.define('a', 2)
    >>> frame1.define('c', 3)
    >>> frame1.lookup('a')
    2
    >>> frame1.lookup('b')
    4
    >>> frame1.lookup('c')
    3
    >>> global_frame.lookup('a')
    1
    >>> global_frame.lookup('c') # doctest: +IGNORE_EXCEPTION_DETAIL
    Traceback (most recent call last):
    ...
    SchemeError:
    
    #Problem A9
    >>> env = create_global_frame()
    >>> vals = read_line('( (pow x y) (* x y) )')
    >>> do_define_form(vals, env)
    >>> print(env.lookup('pow'))
    (lambda (x y) (* x y))
    >>> vals = read_line('( (0 x y) (* x y) )')
    >>> do_define_form(vals, env) # doctest: +IGNORE_EXCEPTION_DETAIL
    Traceback (most recent call last):
    ...
    SchemeError:
    """
    
    check_form(vals, 2)
    target = vals[0]
    check_formals(target)
    if scheme_symbolp(target):
        check_form(vals, 2, 2)
        value = scheme_eval(vals[1], env)
        env.define(target, value)
    elif isinstance(target, Pair):
        lam_name = target.first       
        #print(lam_name) #for testing
        lam_formals = target.second
        #print(lam_formals) #fot testing
        lam_body = vals.second
        #print(lam_body) #for testing
        value = do_lambda_form(Pair(lam_formals, lam_body), env)
        env.define(lam_name, value)
    else:
        raise SchemeError("bad argument to define")

def do_quote_form(vals):
    """Evaluate a quote form with parameters VALS."""
    check_form(vals, 1, 1)
    return vals[0]

def do_let_form(vals, env):
    """Evaluate a let form with parameters VALS in environment ENV."""
    check_form(vals, 2)
    bindings = vals[0]
    exprs = vals.second
    if not scheme_listp(bindings):
        raise SchemeError("bad bindings list in let form")

    # Add a frame containing bindings
    names, vals = nil, nil
    for binding in bindings:
        check_form(binding,2,2)
        if len(binding) != 2:
            raise SchemeError("let binding error")
        name = binding[0]
        val = scheme_eval(binding[1], env)
        names = Pair(name, names)
        vals = Pair(val, vals)
    check_formals(names)    
    new_env = env.make_call_frame(names, vals)

    # Evaluate all but the last expression after bindings, and return the last
    last = len(exprs)-1
    for i in range(0, last):
        scheme_eval(exprs[i], new_env)
    return exprs[last], new_env

#########################
# Logical Special Forms #
#########################

def do_if_form(vals, env):
    """Evaluate if form with parameters VALS in environment ENV."""
    check_form(vals, 3, 3)
    eval_cond = scheme_eval(vals.first, env)
    if scheme_true(eval_cond):
        return vals.second.first
    else:
        return vals.second.second.first

def do_and_form(vals, env):
    """Evaluate short-circuited and with parameters VALS in environment ENV."""
    if len(vals) == 0:
        return True
    for val in vals:
        eval = scheme_eval(val, env)
        if not scheme_true(eval):
            return False
    return val

def do_or_form(vals, env):
    """Evaluate short-circuited or with parameters VALS in environment ENV."""
    for val in vals:
        eval = scheme_eval(val, env)
        if scheme_true(eval):
            return val
    return False

def do_cond_form(vals, env):
    """Evaluate cond form with parameters VALS in environment ENV."""
    num_clauses = len(vals)
    for i, clause in enumerate(vals):
        check_form(clause, 1)
        if clause.first == "else":
            if i < num_clauses-1:
                raise SchemeError("else must be last")
            test = True
            if clause.second is nil:
                raise SchemeError("badly formed else clause")
        else:
            test = scheme_eval(clause.first, env)
        if test:
            if len(clause) == 1:
                if scheme_numberp(clause.first) or scheme_symbolp(clause.first):
                    return clause.first
                return True
            if len(clause) == 2:
                return clause.second.first
            if len(clause) > 2:
                return do_begin_form(clause.second, env)

def do_begin_form(vals, env):
    """Evaluate begin form with parameters VALS in environment ENV."""
    check_form(vals, 1)
    if vals.second is nil:
        return vals.first
    else:
        scheme_eval(vals.first, env)
        return do_begin_form(vals.second, env)

LOGIC_FORMS = {
        "and": do_and_form,
        "or": do_or_form,
        "if": do_if_form,
        "cond": do_cond_form,
        "begin": do_begin_form,
        }

# Utility methods for checking the structure of Scheme programs

def check_form(expr, min, max = None):
    """Check EXPR (default SELF.expr) is a proper list whose length is
    at least MIN and no more than MAX (default: no maximum). Raises
    a SchemeError if this is not the case."""
    if not scheme_listp(expr):
        raise SchemeError("badly formed expression: " + str(expr))
    length = len(expr)
    if length < min:
        raise SchemeError("too few operands in form")
    elif max is not None and length > max:
        raise SchemeError("too many operands in form")

def check_formals(formals):
    """Check that FORMALS is a valid parameter list, a Scheme list of symbols
    in which each symbol is distinct.

    >>> check_formals(read_line("(a b c)"))
    >>> check_formals(read_line("(a . b)")) # doctest: +IGNORE_EXCEPTION_DETAIL
    Traceback (most recent call last):
    ...
    SchemeError:
    >>> check_formals(read_line("(a b c a)")) # doctest: +IGNORE_EXCEPTION_DETAIL
    Traceback (most recent call last):
    ...
    SchemeError:
    >>> check_formals(read_line("(a b 0 c)")) # doctest: +IGNORE_EXCEPTION_DETAIL
    Traceback (most recent call last):
    ...
    SchemeError:
    >>> check_formals(read_line("()"))
    """
    formal_symbols = []
    def check_sym_helper(symbol):
        if not scheme_symbolp(symbol):
            raise SchemeError('Invaild symbol')
        elif symbol in formal_symbols:
            raise SchemeError('Repeated symbol')
        elif not scheme_listp(formals):
            raise SchemeError('Not a well-formed list')       
        formal_symbols.append(symbol)
        
    while isinstance(formals, Pair) and formals != nil:
        check_sym_helper(formals.first)
        formals = formals.second


##################
# Tail Recursion #
##################

def scheme_optimized_eval(expr, env):
    """Evaluate Scheme expression EXPR in environment ENV."""
    while True:
        if expr is None:
            raise SchemeError("Cannot evaluate an undefined expression.")

        # Evaluate Atoms
        if scheme_symbolp(expr):
            return env.lookup(expr)
        elif scheme_atomp(expr):
            return expr

        # All non-atomic expressions are lists.
        if not scheme_listp(expr):
            raise SchemeError("malformed list: {0}".format(str(expr)))
        first, rest = expr.first, expr.second

        # Evaluate Combinations
        if first in LOGIC_FORMS:
            expr = LOGIC_FORMS[first](rest, env)
        elif first == "lambda":
            return do_lambda_form(rest, env)
        elif first == "mu":
            return do_mu_form(rest)
        elif first == "define":
            return do_define_form(rest, env)
        elif first == "quote":
            return do_quote_form(rest)
        elif first == "let":
            expr, env = do_let_form(rest, env)
        else:
            new_procedure = scheme_optimized_eval(first, env)
            args = rest.map(lambda operand: scheme_optimized_eval(operand, env))
            if isinstance(new_procedure, LambdaProcedure):
                expr = new_procedure.body
                env = new_procedure.env.make_call_frame(new_procedure.formals, args)
            elif isinstance(new_procedure, MuProcedure):
                expr = new_procedure.body
                env = env.make_call_frame(new_procedure.formals, args)
            elif isinstance(new_procedure, PrimitiveProcedure):
                return scheme_apply(new_procedure, args, env)
            else:
                raise SchemeError("not alble to call {0}".format(str(new_procedure)))

################################################################
# Uncomment the following line to apply tail call optimization #
################################################################
scheme_eval = scheme_optimized_eval


################
# Input/Output #
################

def read_eval_print_loop(next_line, env):
    """Read and evaluate input until an end of file or keyboard interrupt."""
    while True:
        try:
            src = next_line()
            while src.more_on_line:
                expression = scheme_read(src)
                result = scheme_eval(expression, env)
                if result is not None:
                    print(result)
        except (SchemeError, SyntaxError, ValueError) as err:
            print("Error:", err)
        except (KeyboardInterrupt, EOFError):  # <Control>-D, etc.
            return

def scheme_load(sym, env):
    """Load Scheme source file named SYM in environment ENV."""
    check_type(sym, scheme_symbolp, 0, "load")
    with scheme_open(sym) as infile:
        lines = infile.readlines()
    def next_line():
        return buffer_lines(lines)
    read_eval_print_loop(next_line, env.global_frame())

def scheme_open(filename):
    """If either FILENAME or FILENAME.scm is the name of a valid file,
    return a Python file opened to it. Otherwise, raise an error."""
    try:
        return open(filename)
    except IOError as exc:
        if filename.endswith('.scm'):
            raise SchemeError(str(exc))
    try:
        return open(filename + '.scm')
    except IOError as exc:
        raise SchemeError(str(exc))

def create_global_frame():
    """Initialize and return a single-frame environment with built-in names."""
    env = Frame(None)
    env.define("eval", PrimitiveProcedure(scheme_eval, True))
    env.define("apply", PrimitiveProcedure(scheme_apply, True))
    env.define("load", PrimitiveProcedure(scheme_load, True))
    add_primitives(env)
    return env

@main
def run(*argv):
    next_line = buffer_input
    if argv:
        try:
            filename = argv[0]
            input_file = open(argv[0])
            lines = input_file.readlines()
            def next_line():
                return buffer_lines(lines)
        except IOError as err:
            print(err)
            sys.exit(1)
    read_eval_print_loop(next_line, create_global_frame())

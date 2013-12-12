module Wat

  module VM

    extend self
    def self.struct(*names, &block)
      struct = names.empty? ? Class.new { include VM } : Struct.new(*names) { include VM }
      struct.module_eval(&block) if block
      struct
    end

    ###
    # Continuations
    ###

    Continuation = struct(:fun, :next)

    def continuation?(x)
      x.kind_of? Continuation
    end

    Capture = struct(:prompt, :handler, :k)

    def capture?(x)
      x.kind_of? Capture
    end

    def capt(c, fun, e = nil, *o)
      if capture?(c)
        fun = lambda { |k,f| fun.to_proc.call(e, k, f, *o) } unless fun.is_a?(Proc)
        capture_frame(c, fun)
        c
      elsif block_given?
        yield
      end
    end

    def capture_frame(capture, fun = nil, &block)
      capture.k = Continuation.new(fun || block, capture.k)
    end

    def continue_frame(k, f)
      k.fun.call(k.next, f)
    end

    def cont(k, f)
      if continuation?(k)
        continue_frame(k, f)
      elsif block_given?
        yield
      end
    end


    ###
    # Evaluation Core
    ###
    def evaluate(e, k, f, x)
      x && x.respond_to?(:wat_eval) && x.wat_eval(e, k, f) || x
    end

    Sym = struct(:name) do
      def wat_eval(e, k, f)
        lookup(e, name)
      end
    end

    Cons = struct(:car, :cdr) do
      def car
        self[:car]
      end
      def cdr
        self[:cdr]
      end
      def wat_eval(e, k, f)
        op = cont(k,f) { evaluate(e, nil, nil, car) }
        capt(op, :wat_eval, e) { combine(e, nil, nil, op, cdr) }
      end
    end

    ###
    # Operative & Applicative Combiners
    ###

    def combine(e, k, f, cmb, o)
      if cmb && cmb.respond_to?(:wat_combine)
        cmb.wat_combine(e, k, f, o)
      else
        fail "Not a combiner: #{cmb.wat_inspect}"
      end
    end

    def wrap(cmb)
      Apv.new(cmb)
    end

    def unwrap(apv)
      apv.cmb
    end

    Opv = struct(:p, :ep, :x, :e) do
      def wat_combine(e, k, f, o) 
        xe = make_env(self.e)
        bind(xe, p, o)
        bind(xe, ep, e)
        evaluate(xe, k, f, x)
      end
    end

    Apv = struct(:cmb) do
      def wat_combine(e, k, f, o)
        args = cont(k,f) { eval_args(e, nil, nil, o, NIL) }
        capt(args, :wat_combine, e, o) { cmb.wat_combine(e, nil, nil, args) }
      end
    end

    def eval_args(e, k, f, todo, done)
      return reverse_list(done) if todo == NIL
      arg = cont(k,f) { evaluate(e, nil, nil, car(todo)) }
      capt(arg, :eval_args, e, todo, done) { eval_args(e, nil, nil, cdr(todo), cons(arg, done)) }
    end


    ###
    # Built-in Combiners
    ###
    Vau = struct do
      def wat_combine(e, k, f, o)
        Opv.new(elt(o, 0), elt(o, 1), elt(o, 2), e)
      end
    end

    Def = struct do
      def wat_combine(e, k, f, o)
        val = cont(k,f) { evaluate(e, nil, nil, elt(o, 1)) }
        capt(val, :wat_combine, e, o) { bind(e, elt(o, 0), val) }
      end
    end

    Eval = struct do
      def wat_combine(e, k, f, o)
        evaluate(elt(o, 1), k, f, elt(o, 0))
      end
    end


    ###
    # First-order Control
    ###
    Begin = struct do
      def wat_combine(e, k, f, o)
        o == NIL ? nil : self.begin(e, k, f, o)
      end
    end

    def begin(e, k, f, xs)
      res = cont(k,f) { evaluate(e, nil, nil, car(xs)) }
      capt(res, :begin, e, xs) do
        kdr = cdr(xs)
        kdr == NIL ? res : self.begin(e, nil, nil, kdr)
      end
    end

    If = struct do
      def wat_combine(e, k, f, o)
        test = cont(k,f) { evaluate(e, nil, nil, elt(o, 0)) }
        capt(test, :wat_combine, e, o) do 
          evaluate(e, nil, nil, test ? elt(o, 1) : elt(o, 2))
        end
      end
    end

    Loop = struct do
      def wat_combine(e, k, f, o)
        first = true # only continue once
        loop do
          rest = first && cont(k,f) { evaluate(e, nil, nil, elt(o, 0)) }
          first = false
          capt(res, :wat_combine, e, o)
        end
      end
    end

    Catch = struct do
      def wat_combine(e, k, f, o)
        th = elt(o, 0)
        handler = elt(o, 1)
        begin
          res = cont(k,f) { combine(e, nil, nil, th, NIL) }
        rescue => exc
          # unwrap handler to prevent eval if exc is sym or cons
          res = combine(e, nil, nil, unwrap(handler), list(exc))
        end
        capt(res, :wat_combine, e, o) { res }
      end
    end

    Finally = struct do
      def wat_combine(e, k, f, o)
        prot = elt(o, 0)
        cleanup = elt(o, 1)
        begin
          res = cont(k,f) { evaluate(e, nil, nil, prot) }
          capt(res, :wat_combine, e, o)
        ensure
          capture?(res) ? res : do_cleanup(e, nil, nil, cleanup, res)
        end
      end
    end

    def do_cleanup(e, k, f, cleanup, res)
      fres = cont(k,f) { evaluate(e, nil, nil, cleanup) }
      capt(fres, :do_cleanup, e, cleanup) { res }
    end

    ###
    # Delimited Control
    ###

    PushPrompt = struct do
      def wat_combine(e, k, f, o)
        prompt, th = elt(o, 0), elt(o, 1)
        res = cont(k,f) { combine(e, nil, nil, th, NIL) }
        if capture?(res)
          if res.prompt == prompt
            continuation, handler = res.k, res.handler
            combine(e, nil, nil, handler, cons(continuation, NIL))
          else
            capture_frame(res) { |k,f| wat_combine(e,k,f,o) }
            res
          end
        else
          res
        end
      end
    end

    TakeSubcont = struct do
      def wat_combine(e, k, f, o)
        prompt, handler = elt(o, 0), elt(o, 1)
        cap = Capture.new(prompt, handler)
        capture_frame(cap) { |k,thef| combine(e, nil, nil, thef, NIL)}
        cap
      end
    end

    PushSubcont = struct do
      def wat_combine(e, k, f, o)
        thek, thef = elt(o, 0), elt(o, 1)
        res = cont(k,f) { continue_frame(thek, thef) }
        capt(res, :wat_combine, e, o) { res }
      end
    end

    ###
    # Dynamic Variables
    ###

    DV = struct(:val)

    DNew = struct do
      def wat_combine(e, k, f, o)
        DV.new(elt(o, 0))
      end
    end

    DRef = struct do
      def wat_combine(e, k, f, o)
        elt(o, 0).val
      end
    end

    DLet = struct do
      def wat_combine(e, k, f, o)
        dv, val, th = elt(o, 0), elt(o, 1), elt(o, 2)
        old_val = dv.val
        dv.val = val
        begin
          res = cont(k,f) { combine(e, nil, nil, th, NIL) }
          capt(res, :wat_combine, e, o) { res }
        ensure
          dv.val = old_val
        end
      end
    end

    ###
    # Objects
    ###

    Nil = struct do
      def car
        NIL
      end

      def cdr
        NIL
      end
    end

    Ign = struct

    NIL = Nil.new
    IGN = Ign.new

    def cons(car, cdr)
      Cons.new(car, cdr)
    end

    def car(cons)
      cons.car
    end

    def cdr(cons)
      cons.cdr
    end

    def elt(cons, i)
      i.zero? ? car(cons) : elt(cdr(cons), i - 1)
    end

    def sym_name(sym)
      sym.name
    end

    Env = struct do
      def initialize(parent = nil)
        @bindings = {}
        @parent  = parent || {}
      end

      def [](key)
        @bindings[key] || @parent[key]
      end

      def store(key, value)
        @bindings.store(key, value)
      end

      def include?(name)
        @bindings.include?(name) || @parent.include?(name)
      end
    end

    def make_env(parent = {})
      Env.new(parent) 
    end

    def lookup(e, name)
      if e.include?(name)
        e[name]
      else
        fail "unbound: #{name}"
      end
    end

    def bind(e, lhs, rhs)
      lhs.wat_match(e, rhs)
      rhs
    end

    class Sym
      def wat_match(e, rhs)
        if e.nil?
          fail("undefined argument: #{name}")
        else
          e.store(name, rhs)
        end
      end
    end

    class Cons
      def wat_match(e, rhs)
        car.wat_match(e, VM.car(rhs))
        cdr.wat_match(e, VM.cdr(rhs))
      end
    end

    class Nil
      def wat_match(e, rhs)
        unless rhs == NIL
          fail("NIL expected, but got: "+rhs.wat_inspect)
        end
      end
    end

    class Ign
      def wat_match(e, rhs)
      end
    end

    ###
    # Utilities
    ###

    def fail(err)
      raise err
    end

    def list(*args)
      array_to_list args
    end

    def list_star(*args)
      args.reverse.drop(1).inject(args.last || NIL) { |c,i| cons(i, c) }
    end

    def array_to_list(array, _end = NIL)
      array.reverse.inject(_end) { |c,i| cons(i, c) }
    end

    def list_to_array(c)
      array = []
      while c != NIL
        array.push car(c)
        c = cdr(c)
      end
      array
    end

    def reverse_list(c)
      reverse = NIL
      while c != NIL
        reverse = cons(car(c), reverse)
        c = cdr(c)
      end
      reverse
    end

    ###
    # Parser
    ###

    def parse_json_value(obj)
      return NIL if obj.nil?

      if obj.kind_of?(String) || obj.kind_of?(Symbol)
        if obj.to_s == "#ignore"
          return IGN
        else
          return Sym.new(obj.to_s)
        end
      end

      if obj.kind_of?(Array)
        return parse_json_array(obj)
      end

      obj
    end

    def parse_json_array(arr)
      i = arr.index("#rest")

      unless i
        return array_to_list arr.map { |a| parse_json_value(a) }
      end

      front = arr.slice(0, i).map { |a| parse_json_value(a) }
      array_to_list(front, parse_json_value(arr[i.succ]))
    end

    ###
    # RBNI
    ###

    RBFun = struct(:callable) do 
      def initialize(callable)
        unless callable.respond_to?(:call)
          if callable.respond_to?(:to_proc)
            callable = callable.to_proc
          else
            fail "no fun"
          end
        end
        super(callable)
      end

      def wat_combine(e, k, f, o)
        callable.call(*list_to_array(o))
      end
    end

    def rb_wrap(callable = nil, &block)
      wrap RBFun.new(callable || block)
    end

    def rb_unop(op)
      rb_wrap lambda { |a| a.send("#{op}@") }
    end

    def rb_binop(op)
      rb_wrap lambda { |a, b| a.send(op, b) }
    end

    def rb_invoke(obj, method_name, *args, &block)
      obj.send(method_name, *args, &block)
    end

    def rb_callback(cmb)
      lambda do |*args|
        args = array_to_list(args)
        combine(make_env, nil, nil, cmb, args)
      end
    end

    ###
    # Primitives
    ###

    Primitives = [
      "begin",
       # Core

       # Fexprs
       ["def", "--vau", Vau.new],
       ["def", "eval", wrap(Eval.new)],
       ["def", "make-environment", rb_wrap { make_env }],
       ["def", "wrap", rb_wrap(method(:wrap))],
       ["def", "unwrap", rb_wrap(method(:unwrap))],
       # Values
       ["def", "cons", rb_wrap(method(:cons))],
       ["def", "cons?", rb_wrap {|o| o.kind_of?(Cons) }],
       ["def", "nil?", rb_wrap {|o| o == NIL }],
       ["def", "symbol?", rb_wrap {|o| o.kind_of?(Sym) }],
       ["def", "symbol-name", rb_wrap(method(:sym_name))],
       # First-order Control
       ["def", "if", If.new],
       ["def", "--loop", Loop.new],
       ["def", "throw", rb_wrap(method(:fail))],
       ["def", "--catch", wrap(Catch.new)],
       ["def", "finally", Finally.new],
       # Delimited Control
       ["def", "--push-prompt", wrap(PushPrompt.new)],
       ["def", "--take-subcont", wrap(TakeSubcont.new)],
       ["def", "--push-subcont", wrap(PushSubcont.new)],
       # Dynamically-scoped Variables
       ["def", "dnew", wrap(DNew.new)],
       ["def", "--dlet", wrap(DLet.new)],
       ["def", "dref", wrap(DRef.new)],
       # RB Interface
       ["def", "rb-wrap", rb_wrap(method(:rb_wrap))],
       ["def", "rb-unop", rb_wrap(method(:rb_unop))],
       ["def", "rb-binop", rb_wrap(method(:rb_binop))],
       ["def", "rb-element", rb_wrap {|obj,i| obj[i] }],
       ["def", "rb-set-element", rb_wrap {|obj, i, v| obj[i] = v}],
       ["def", "rb-invoke", rb_wrap(method(:rb_invoke))],
       ["def", "rb-callback", rb_wrap(method(:rb_callback))],
       ["def", "list-to-array", rb_wrap(method(:list_to_array))],
       # Optimization
       ["def", "list*", rb_wrap(method(:list_star))],

       # Primitives

       ["def", "quote", ["--vau", ["x"], "#ignore", "x"]],
       ["def", "list", ["wrap", ["--vau", "arglist", "#ignore", "arglist"]]],
       ["def", "string", ["--vau", ["sym"], "#ignore", ["symbol-name", "sym"]]],
       ["def", "get-current-environment", ["--vau", [], "e", "e"]],

       ["def", "make-macro-expander",
        ["wrap",
         ["--vau", ["expander"], "#ignore",
         ["--vau", "operands", "env",
           ["eval", ["eval", ["cons", "expander", "operands"], ["make-environment"]], "env"]]]]],

       ["def", "vau",
        ["make-macro-expander",
         ["--vau", ["params", "env-param", "#rest", "body"], "#ignore",
         ["list", "--vau", "params", "env-param", ["cons", "begin", "body"]]]]],

       ["def", "macro",
        ["make-macro-expander",
         ["vau", ["params", "#rest", "body"], "#ignore",
         ["list", "make-macro-expander", ["list*", "vau", "params", "#ignore", "body"]]]]],

       ["def", "lambda",
        ["macro", ["params", "#rest", "body"],
        ["list", "wrap", ["list*", "vau", "params", "#ignore", "body"]]]],

       ["def", "loop",
        ["macro", "body",
         ["list", "--loop", ["list*", "begin", "body"]]]],

       ["def", "catch",
        ["macro", ["protected", "handler"],
        ["list", "--catch", ["list", "lambda", [], "protected"], "handler"]]],

       ["def", "push-prompt",
        ["macro", ["prompt", "#rest", "body"],
        ["list", "--push-prompt", "prompt", ["list*", "lambda", [], "body"]]]],

       ["def", "take-subcont",
        ["macro", ["prompt", "k", "#rest", "body"],
        ["list", "--take-subcont", "prompt", ["list*", "lambda", ["list", "k"], "body"]]]],

       ["def", "push-subcont",
        ["macro", ["k", "#rest", "body"],
        ["list", "--push-subcont", "k", ["list*", "lambda", [], "body"]]]],

       # RB

       ["def", "array", ["lambda", "args", ["list-to-array", "args"]]],

       ["def", "define-rb-unop",
        ["macro", ["op"],
        ["list", "def", "op", ["list", "rb-unop", ["list", "string", "op"]]]]],

        ["define-rb-unop", "!"],
        ["define-rb-unop", "+"],
        ["define-rb-unop", "-"],
        ["define-rb-unop", "~"],

        ["def", "define-rb-binop",
          ["macro", ["op"],
          ["list", "def", "op", ["list", "rb-binop", ["list", "string", "op"]]]]],

        ["define-rb-binop", "+"],
        ["define-rb-binop", "-"],
        ["define-rb-binop", "*"],
        ["define-rb-binop", "/"],
        ["define-rb-binop", "%"],
        ["define-rb-binop", "**"],
        ["define-rb-binop", "=="],
        ["define-rb-binop", "!="],
        ["define-rb-binop", "||"],
        ["define-rb-binop", "&&"],
        ["define-rb-binop", ">"],
        ["define-rb-binop", "<"],
        ["define-rb-binop", ">="],
        ["define-rb-binop", "<="],
        ["define-rb-binop", "<=>"],
        ["define-rb-binop", "==="],
        ["define-rb-binop", "="],
        ["define-rb-binop", "+="],
        ["define-rb-binop", "-="],
        ["define-rb-binop", "*="],
        ["define-rb-binop", "/="],
        ["define-rb-binop", "%="],
        ["define-rb-binop", "**="],

        ["def", ".",
          ["macro", ["field", "obj"],
          ["list", "rb-element", "obj", ["list", "string", "field"]]]],

        ["def", "#",
          ["macro", ["method", "obj", "#rest", "args"],
          ["list*", "rb-invoke", "obj", ["list", "string", "method"], "args"]]],

    ]

    ###
    # Init
    ### 

    def new
      environment = make_env
      bind(environment, Sym.new("def"), Def.new)
      bind(environment, Sym.new("begin"), Begin.new)
      environment.run(Primitives)
      environment
    end

    ###
    # API
    ###

    class Env
      def run(x)
        evaluate(self, nil, nil, parse_json_value(x))
      end
    end

  end


end

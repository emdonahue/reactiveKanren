"use strict"
import {logging, log, toString, copy, copy_empty, equals, is_string, is_number, is_boolean, is_pojo, assert, subToArray, subToLabels} from './util.js';
//TODO global generic 'model' variable object as a shortcut for (v,m) => v.eq(m), maybe generalize to path vars
//TODO let query variables be added manually not just extracted from fresh
//TODO use clone node over create element for speed when applicable (eg dynamic model)
//TODO look into event delegation
//TODO can we generalize LCS to use partial reuse instead of binary equality
//TODO reuse old node even on new template in case it has some common sub templates (eg can reuse a text node we are about to throw away just by textContent =)
//TODO rewrite entire mk engine to be non recursive to handle large cases
//TODO for an iterable, create an entire subtree with all sub-iterables generating only 1 copy, then clone that node and reuse it across all subsequent iterations
//TODO give lvar an .orderby method that constructs a view ordered by whatever that binds to. then even if its bound multiply we just produce sibling dynamic sets ordered by different fns
//TODO dont have to pass mvar anymore with lexical scope
//TODO can reactive unify assign a concrete timestep so we can set fresh vars and resolve conflicting unifies by checking timestep, even if they conflict with source code goals/model vars?
//TODO have compiler strip all asserts, errors, tostrings, so ensure each is on its own line
//TODO replace tagName with tag or something shorter
//TODO add an 'abbrev' object to RK that translates tag -> tagName, class -> className by default but can be adjusted by user

//diffing
//if dynamic nodes are unsorted, then we know that they can only insert or remove, not reorder? no, the model might change
//check out https://github.com/facebook/react/issues/10382
//if only additions, no diffing needed. if only deletions, no diffing needed.
//cloning only makes sense if templates arent recursive, so is there a way to check/annotate that? maybe recursiveness could trigger more advanced diffing, since each subtree may have to trash the previous structurally distinct subtree. alternatively, maybe we only clone the parent stump and then children overwrite the placeholders (can use comments or text nodes as placeholders, and then if the placeholder turns out to be a text node, we're already done, otherwise we just sacrifice a textnode

//TODO implement property list dom nodes
//TODO implement iterable children of dom nodes
//TODO implement static var children of dom nodes
//TODO implement dynamic properties as children of dom nodes

// TYPES

function is_text(x) { return is_string(x) || is_number(x) || is_boolean(x); }

// APP INTERFACE
class RK {
    constructor(template, data) {
        this.mvar = new MVar().name('model');
        this.substitution = this.mvar.set(data).rediff(); //TODO can we have an app init where we enrich with local vars (selected/editing flags) then track which vars were added and shed them when sending data outside? maybe tagged LVars for locals
        log('render', this.constructor.name, 'substitution', subToArray(this.substitution));
        this.template = (template instanceof Function) ? template(this.mvar) : template;
        this.child = View.render(this.substitution, this, this.template);
    }
    root() { return this.child.root(); }
    rerender(g) {//TODO rename this to be part of the rerender chain and provide a different user-facing api
        if (g instanceof Function) return this.rerender(g(this.mvar));
        this.update(g, this.substitution);
        return this;
    }
    update(patch) { //TODO rename update->set
        if (patch.isNil()) return;
        log('reunify', this.constructor.name, subToArray(patch), subToArray(this.substitution));
        this.substitution = patch.repatch(this.substitution);
        log('rerender', this.constructor.name, subToArray(this.substitution));
        this.child = this.child.rerender(this.substitution, this);
    }
    toString() { return `(RK ${this.child})` }}



// Lists
class List {
    [Symbol.iterator]() { return this.toArray()[Symbol.iterator](); }
    length() { return this.toArray().length; }
    ref(n) {
        let self = this;
        while (self instanceof Pair && 0 < n--) { self = self.cdr; }
        return self.car; }
    asDiff() { return this; }
    cons(e) { return new Pair(e, this); }
    acons(k, v) { return this.cons(new Pair(k, v)); }
    extend(k, v) { //TODO make a separate filter(remove) based extend for reactive
        return this.filter(x => x.car != k).acons(k, v);
    }
    member(e) {
        return this.memp(x => x == e);
    }
    unassoc(key) { return this.filter(x => x.car !== key); }
    assoc(key) {
        let self = this;
        while (self instanceof Pair) {
            if (self.car instanceof Pair && self.car.car === key) return self.car;
            self = self.cdr;
        }
        return undefined;
    }
    sort(f) { return list(...this.toArray().sort(f)); }
    static repeat(n, f) {
        return nil.repeat(n, f);
    }
    isFailure() { return false; }
    repeat(n, f) {
        if (n <= 0) return this;
        return this.cons(f()).repeat(n-1, f);
    }
    join(sep='') {
        let self = this, first = true, str;
        while (self instanceof Pair) {
            if (first) str = self.car;
            else str += sep + self.car;
            first = false;
            self = self.cdr; }
        return str; }
    filter(p) {
        let self = this, head = null, tail = null;
        while (self instanceof Pair) {
            if (p(self.car)) {
                if (!head)  tail = head = new Pair(self.car, null);
                else tail = tail.cdr = new Pair(self.car, null); }
            self = self.cdr; }
        if (tail) tail.cdr = self;
        else head = self;
        return head;
    }
    walk(lvar, walk_mvars=true) { return this.walk_binding(lvar, walk_mvars).cdr; }
    walk_binding(lvar, walk_mvars=true) {
        if (!(lvar instanceof LVar) || !walk_mvars && lvar instanceof MVar) return new Pair(lvar, lvar);
        const v = this.assoc(lvar);
        if (v) { return (v.cdr instanceof LVar) ? this.walk_binding(v.cdr, walk_mvars) : v; }
        else return new Pair(lvar, lvar); }
    reify(lvar, walk_mvars=true) {
        if (arguments.length == 0) return this.map((b) => new Pair(b.car, this.reify(b.cdr, walk_mvars))); //TODO make this its own debug thing?
        if (!walk_mvars && lvar instanceof MVar) return lvar;
        let v = this.walk(lvar, walk_mvars);
        if (v instanceof LVar || primitive(v)) return v;
        if (v instanceof QuotedVar) return this.reify(v.lvar, walk_mvars);
        if (v instanceof Pair) return new Pair(this.reify(v.car, walk_mvars), this.reify(v.cdr, walk_mvars));
        if (Array.isArray(v)) return v.map(e => this.reify(e, walk_mvars));
        return Object.fromEntries(Object.entries(v).map(([k,v]) => [k, this.reify(v, walk_mvars)]));
    }
    toState(updates) { return new State(this, updates); }
    toString() { return '(' + this._toString() + ')'; }
    unify(x_var, y_var) { // unifier has to be very lazy about preserving variable paths and not updating to latest value
        let x, y; //TODO make a classic unifier mode and use it when unifying all the updates to create the diff, since they no longer need to preserve provenance
        ({car: x_var, cdr: x} = this.walk_binding(x_var));
        ({car: y_var, cdr: y} = this.walk_binding(y_var));
        log('unify', x_var, x, y_var, y);
        if (x === y) {
            if (x instanceof LVar || x_var === y_var) return this; // Vars already in same equivalence class: share lowest variable or just ground terms.
            else if (x_var instanceof LVar) return this.extend(x_var, y_var); // Align vars to same equivalence class
            else return this.extend(y_var, x_var); }
        if (x instanceof LVar) return this.extend(x, y_var); // Align to equivalence class, not bound value.
        if (y instanceof LVar) return this.extend(y, x_var);
        if (primitive(x) || primitive(y)) return failure; // Primitives but not ===
        if (Object.getPrototypeOf(x) !== Object.getPrototypeOf(y)) return failure;
        let s = this;
        for (let k of Object.keys(x).filter(k => Object.hasOwn(y, k))) {
            s = s.unify(x[k], y[k]);
            if (s.isFailure()) return failure;
        }
        return s;
    }
    repatch(sub=nil) { return this.fold((s, p) => s.extend(p.car, p.cdr), sub); }}
function list(...xs) { return cons(...xs, nil); }
function cons(...xs) { return xs.reduceRight((x,y) => new Pair(y, x)); }

class Pair extends List {
    constructor(car, cdr) {
	super();
	this.car = car;
	this.cdr = cdr;
    }
    caar() { return this.car.car; }
    cdar() { return this.car.cdr; }
    toArray() {
        return [this.car].concat((this.cdr instanceof List) ? this.cdr.toArray() : [this.cdr]);
    }
    firstAnswer() { return this.car.substitution; }
    memp(p) {
        if (p(this.car)) return this.car;
        return this.cdr.memp(p);
    }
    remove(x) {
        if (this.car == x) return this.cdr;
        return this.cdr.remove(x).cons(this.car);
    }
    map(f) {
        return this.cdr.map(f).cons(f(this.car));
    }
    fold(f, x) {
        return this.cdr.fold(f, f(x, this.car));
    }
    append(xs) {
        return new Pair(this.car, this.cdr.append(xs));
    }
    every(f) {
        f(this.car);
        this.cdr.every(f);
        return this; }
    isNil() { return false; }

    // x->1, y->2


    _toString() {
        window.lst = this; //TODO remove tostring debugging reference
        return `${toString(this.car)}${this.cdr instanceof Pair ? ' ' : ''}${this.cdr instanceof List ? this.cdr._toString() : ' . ' + toString(this.cdr)}`;
    }
}

class Empty extends List {
    toArray() {
        return [];
    }

    memp(p) { return undefined; };
    map(f) { return this; };
    update_substitution(s) { return s; }
    append(xs) { return xs; }
    isNil() { return true; }
    fold(f, x) { return x; }
    remove(x) { return this; }
    firstAnswer() { return failure; }
    every(f) { return this; }
    _toString() { return ''; }
}

// Vars & Data
class LVar {
    static id = 0;
    constructor(name='') {
        assert(is_string(name));
	this.id = LVar.id++;
        this.label = name;
    }
    toString() {
        return `<${this.label}${this.label ? ':' : ''}${this.id}>`;
    }
    eq(x) { return eq(this, x); }
    set(x) { return new Reunification(this, x); }
    put(x) { return new Reunification(this, x, true); }
    patch(x) { return new Reunification(this, x, true, true); }
    name(n) { this.label = n; return this; }
    quote() { return new QuotedVar(this); }
    constraint(f, ...lvars) { return new Constraint(f, this, ...lvars); }
    isStringo() { return this.constraint(v => is_string(v)); }
    isNumbero() { return this.constraint(v => is_number(v)); }
    isPairo() { return this.constraint(v => v instanceof Pair); }
    isNotPairo() { return this.constraint(v => !(v instanceof Pair)); }
    membero(x) { return fresh((a,b) => [this.eq(cons(a,b)), conde(a.eq(x), b.membero(x))]); }
    negate() { return conde([this.eq(true), this.set(false)], [this.eq(false), this.set(true)]); } //TODO make negate falsy
    leafo(x) { return conde([this.isNotPairo(), this.eq(x)],
                            [fresh((a,b) => [this.eq(cons(a,b)), conde(a.leafo(x), b.leafo(x))])]); }
    imembero(x,o,n=0) { return fresh((a,b) => [this.eq(cons(a,b)), conde([a.eq(x), o.eq(n)], b.imembero(x,o,n+1))]); } //TODO make imembero accept ground order terms
    tailo(x) { return conde(x.eq(this), fresh((a,d) => [this.eq(cons(a,d)), d.tailo(x)])) }}
function eq(x, y) { return new Unification(x, y); }

class MVar extends LVar {
    toString() { return `[${this.label}${this.label ? ':' : ''}${this.id}]`; }
}

class QuotedVar {
    constructor(lvar) {
        this.lvar = lvar;
    }
    toString() { return `"${this.lvar}"`; };
}

// Goals
function primitive(x) {
    return is_string(x) || is_boolean(x) || is_number(x) || x === nil || x === null || x === undefined || x instanceof Function;
}

class Goal {
    static as_goal(g) {
        if (Array.isArray(g)) return g.reduceRight((cs, c) => Goal.as_goal(c).conj(Goal.as_goal(cs)));
        else if (true === g) return succeed;
        else if (!g) return fail;
        else return g; }
    conj(...xs) { return conj(this, ...xs); }
    conde(...g) { return conde(this, ...g); }
    filter(f) { return f(this) ? this : succeed; }
    run(n=-1, {reify=nil, substitution=nil}={}) {
        return this.eval(new State(substitution)).take(n).map(s => reify ? log('run', 'reify', s.substitution.reify(reify)) : s);

    }
    expand_run(s=nil, v=[]) { //TODO remove default viewleaf
        return this.expand(new State(s), succeed, succeed, v);
    }
    cont(s) { return s.isFailure() ? failure : this.eval(s); }
    expand_ctn(s, cjs, v) {
        log('expand', 'ctn', this+'', cjs, toString(s?.substitution));
        return s.isFailure() ? v(cjs.conj(this)) : this.expand(s, succeed, cjs, v); }
    suspend(s) { return new Suspended(s, this) }
    apply(sub) { return sub.isFailure() ? failure : this.run(1, {reify: false, substitution: sub}).firstAnswer(); }
    is_disj() { return false; }
    rediff(sub=nil) {
        assert(sub);
        log('reunify', 'rediff', subToArray(sub));
        let diff = this.run(-1, {reify: false, substitution: sub})
            .fold((s,a) => a.rediff(s), nil).asDiff();
        return diff.map(d => cons(d.car, diff.reify(d.cdr, false)))
            .filter(d => d.car instanceof MVar); }
    toString() { return JSON.stringify(this); }}

function conde(...condes) { return condes.reduceRight((cs, c) => Conde.conde(Goal.as_goal(c), cs), fail); }

function conj(...conjs) { return conjs.reduceRight((cs, c) => Conj.conj(Goal.as_goal(c), cs), succeed); }

class Succeed extends Goal {
    eval(s) { return s; }
    suspend(s, ctn=succeed) { return ctn.cont(s); }
    cont(s) { return s; }
    expand_ctn(s, cjs, [...args]) {
        log('expand', 'return', this+'', cjs, s.substitution+'');
        return AnswerView.render(cjs, s.substitution, ...args);
    }
    expand(s, ctn, cjs, v) { return s.expand_ctn(ctn, cjs, v); }
    toString() { return 'succeed'; }
}

class Fail extends Goal {
    eval(s) { return failure; }
    suspend(s) { return failure; }
    expand(s, ctn, cjs, v) {
        log('expand', 'fail', cjs.conj(ctn));
        return new FailView(cjs.conj(ctn)); }
    toString() { return 'fail'; }
}

class Conj extends Goal {
    constructor(lhs, rhs) {
        super();
        assert(lhs, rhs);
        this.lhs = lhs;
        this.rhs = rhs;
    }
    static conj(x, y) {
        if (x === fail || y === fail) return fail;
        if (x === succeed) return y;
        if (y === succeed) return x;
        return new this(x, y); }
    filter(f) { return this.lhs.filter(f).conj(this.rhs.filter(f)); }
    eval(s, ctn=succeed) {
        return this.lhs.eval(s, this.rhs.conj(ctn));
    }
    expand(s, ctn, cjs, v) {
        log('expand', 'conj', this+'', ctn, cjs);
        return this.lhs.expand(s, this.rhs.conj(ctn), cjs, v);
    }
    toString() { return `(${this.lhs} & ${this.rhs})`; }
}

class Conde extends Goal {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs; }
    static conde(x, y) {
        if (x === fail) return y;
        if (y === fail) return x;
        return new this(x, y); }
    is_disj() { return true; }
    eval(s, ctn=succeed) {
        return this.lhs.eval(s, ctn).mplus(this.rhs.eval(s, ctn));
    }
    expand(s, ctn, cjs, v) {
        log('expand', 'disj', this+'', ctn, cjs);
        return new CondeView(this.lhs.expand(s, ctn, succeed, v), this.rhs.expand(s, ctn, succeed, v), cjs);
    }
    toString() { return `(${this.lhs} | ${this.rhs})`; }
}

class Fresh extends Goal {
    constructor(vars, ctn) {
        super();
        this.vars = vars;
        this.ctn = ctn;
    }
    run(n=-1, {reify=this.vars, ...rest}={}) { return super.run(n, {reify: reify, ...rest}); }
    eval(s, ctn=succeed) {
        return this.instantiate().conj(ctn).suspend(s);
    }
    expand(s, ctn, cjs, v) {
        return this.instantiate().expand(s, ctn, cjs, v);
    }
    instantiate() { return Goal.as_goal(this.ctn(...this.vars)); }
    toString() { return `(fresh ${this.vars} ${this.ctn})`; }
}

class Unification extends Goal {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    eval(s, ctn=succeed) {
        return ctn.cont(s.unify(this.lhs, this.rhs));
    }
    expand(s, ctn, cjs, v) {
        log('expand', '==', this+'', ctn+'', cjs);
        s = s.unify(this.lhs, this.rhs);
        return s.expand_ctn(ctn, cjs.conj(this), v);
    }
    toString() { return `(${toString(this.lhs)} == ${toString(this.rhs)})`; }
}

class Constraint extends Goal {
    constructor(f, ...lvars) {
        super();
        this.lvars = [...lvars];
        this.f = f;
    }
    eval(s, ctn=succeed) {
        if (this.f.apply(null, this.lvars.map(x => s.walk(x)))) return ctn.cont(s);
        return failure;
    }
    expand(sub, ctn, cjs, v) {
        let s = (this.f.apply(null, this.lvars.map(x => sub.walk(x)))) ? sub : failure;
        log('expand', 'constraint', this+'', ctn, cjs, toString(sub?.substitution), s);
        return s.expand_ctn(ctn, cjs.conj(this), v);
    }
    toString() { return `${this.f}(${this.lvars})`; }
}

class Reunification extends Goal {
    constructor(lhs, rhs, put=false, patch=false) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
        this.put = put;
        this.patch = patch; }
    
    diff(sub, deltas, _x=this.lhs, _y=this.rhs) {
        let {car: x_var, cdr: x_varval} = sub.walk_binding(_x, this.put); //TODO may need to revise named destructuring for closure compiler
        assert(x_var instanceof MVar);
        let x = sub.walk(x_varval), y = sub.walk(_y, false);
        log('reunify', this.constructor.name, 'diff', _x, _y, x_var, x, y, toString(deltas), subToArray(sub));
        
        if (equals(x, y)) return deltas; // No changes => no deltas
        if (primitive(y) || y instanceof LVar) return deltas.unify(x_var, y); // Primitive y naively overwrites anything

        let extended = Object.getPrototypeOf(x) !== Object.getPrototypeOf(y); // Will we add properties or change type?
        let x_tended = Object.assign(copy_empty(y), !this.patch || primitive(x) || x instanceof MVar ? {} : x); // Only keep x properties if patching & has them
        
        for (let k in y) { // Patch or create new properties in x for each in y
            if (!(k in x_tended)) { //TODO check on 'in' vs hasOwn
                extended = true; // If we extend the container, we need to update it.
                x_tended[k] = new MVar(); }
            deltas = this.diff(sub, deltas, x_tended[k], y[k]); }
        
        return extended || !this.patch ? deltas.unify(x_var, x_tended) : deltas; }
    
    toString() { return `(${toString(this.lhs)} =${this.patch ? 'patch' : this.put ? 'put' : 'set'}= ${toString(this.rhs)})`; }
    eval(s, ctn=succeed) { return ctn.cont(s.update(this)); }}

function fresh(f) {
    return new Fresh(List.repeat(f.length, () => new LVar()), f);
}

function quote(q) {
    return new QuotedVar(q);
}

// Streams
class Stream {
    mplus(s) { return s._mplus(this); }
    _mplus(s) { return new MPlus(this, s); }
    take(n) {
        if (0 === n || n === -5) return nil; //TODO remove -50 emergency recursion stop
        let s = this;
        while (s.isIncomplete()) { s = s.step(); }
        if (failure == s) return nil;
        log('run', 'take', s.answer());
        return new Pair(s.answer(), s.step().take(n-1));
    }
    isIncomplete() { return true; }
    isFailure() { return false; }
}

class Failure extends Stream {
    unify() { return this; };
    reify(x) { return x; };
    eval(x) { return this; };
    mplus(s) { return s; };
    _mplus(s) { return s; };
    isIncomplete() { return false; }
    step() { return this; }
    isFailure() { return true; }
    toState() { return this; }
    asDiff() { return nil; }
    expand_ctn(ctn, cjs, rtrn) { return new FailView(cjs.conj(ctn)); }
}

class State extends Stream {
    constructor(sub=nil, updates=nil) {
        super();
        assert(sub instanceof List);
        this.substitution = sub;
        this.updates = updates;
    }
    take(n) { return list(this); }
    reify(x) { return this.substitution.reify(x); }
    unify(x, y) { return this.substitution.unify(x, y).toState(this.updates); }
    rediff(sub) { return this.updates.fold((s,u) => u.diff(this.substitution, s), sub); }
    update(u) { return new State(this.substitution, this.updates.cons(u)); }
    extend(x, y) { return new State(this.substitution.extend(x, y), this.updates); }
    eval(g) { return g.eval(this); }
    isIncomplete() { return false; }
    answer() { return this; }
    step() { return failure; }
    mplus(s) { return new Answers(this, s); }
    _mplus(s) { return new Answers(this, s); }
    walk_binding(lvar) { return this.substitution.walk_binding(lvar); }
    walk(lvar) { return this.substitution.walk(lvar); }
    expand_ctn(ctn, cjs, rtrn) { return ctn.expand_ctn(this, cjs, rtrn); }
}

function occurs_check(x,y,s) { // Check if y occurs in x
    if (primitive(x)) return false;

    else if (!(x instanceof LVar)) {
        for (let k in x) {
            if (occurs_check(x[k], y, s)) return true;
        }
    }
    else if (x == y) return true;
    let b = s.assoc(x);
    if (b) return occurs_check(b.cdr,y,s);
    return false;
}


class Suspended extends Stream {
    constructor(s, g) {
        super();
        this.state=s;
        this.goal = g;
    }
    step() { return this.goal.eval(this.state); }
}

class Answers extends Stream {
    constructor(state, stream) {
        super();
        this.state = state;
        this.stream = stream;
    }
    isIncomplete() { return false; }
    answer() { return this.state; }
    step() { return this.stream; }
    mplus(s) { return new Answers(this.state, this.stream.mplus(s)); }
    _mplus(s) { return new Answers(this.state, this.stream.mplus(s)); }
}

class MPlus extends Stream {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    step() {
        return this.lhs.step().mplus(this.rhs);
    }
}

// DOM

class View {
    static render(sub, app, template) {
        assert(template, app instanceof RK);
        if (is_text(template)) return TextView.render(template);
        else if (Array.isArray(template)) return NodeView.render(sub, app, template);
        else return GoalView.render(sub, app, template); }}


class GoalView { //Replaces a child template and generates one sibling node per answer, with templates bound to the view var.
    constructor(vvar, ovar, child, comment=document.createComment('')) {
        assert(comment instanceof Node);
        this.vvar = vvar; // Bound to view templates of each child
        this.ovar = ovar; // Bound to order key of each child
        this.child = child; //Root of tree of views
        this.comment = comment; // Attached to DOM as placeholder if all children fail
    }
    static render(sub, app, template) {
        assert(template, app instanceof RK);
        if (template instanceof LVar) return this.render_lvar(sub, app, template);
        else if (template instanceof Function) return this.render_f(sub, app, template);
        else throw Error(template);
    }
    
    static render_lvar(sub, app, template) {
        log('render', this.name, 'lvar', template, subToArray(sub));
        return new this(template, null, AnswerView.render(succeed, sub, template, app)); }
    
    static render_f(sub, app, f) {
        assert(app instanceof RK)
        let v = new LVar('view').name('view'), o = new LVar().name('order'), g = Goal.as_goal(f(v, o)); // Since o takes up second slot, there's no good api for binding f to 'this' for recursive anonymous functions
        log('render', this.name, 'f', g, subToArray(sub));
        return log('render', this.name + '^', subToArray(sub), new this(v, o, g.expand_run(sub, [v, app]))); }
    
    root() {
        let r = this.child.root();
        if (r instanceof DocumentFragment && !r.childNodes.length) return this.comment;
        return r; }
    sortfn() { return (a,b) => a.order == b.order ? 0 : a.order < b.order ? -1 : 1; }
    subviews(child=this.child) { return child.items().sort(this.sortfn()); }
    rerender(sub, app) {
        log('rerender', this.constructor.name, subToArray(sub));
        let add = [], del = [], nochange = [];

        this.child.firstNode()?.before(this.comment);
        //this.child = this.child.rerender(sub, mvar, this.vvar, add, del, nochange);
        [this.child,] = this.child.rerender(sub, app, this.vvar, this.comment);
        //if (!add.length && !nochange.length) this.child.firstNode().before(this.comment); // Comment placeholder not needed if a real node is in the dom
        //if (add.length || nochange.length) this.comment.remove();
        if (this.child.firstNode()) this.comment.remove();

        for (let item of del) item.remove();
        return this; }

    remove() { this.child.remove(); }
    items(a=[]) {
        this.child.items(a);
        return a; }
    firstNode() { return this.child.firstNode(); }
    lastNode() { return this.child.lastNode(); }
    toString() { return `(root ${this.child})`}}

class CondeView {
    constructor(lhs, rhs, goal) {
        this.goal = goal;
        this.lhs = lhs;
        this.rhs = rhs; }
    root(fragment=document.createDocumentFragment()) {
        this.lhs.root(fragment);
        this.rhs.root(fragment);
        return fragment; }
    remove() {
        this.lhs.remove();
        this.rhs.remove(); }
    toArray(a) {
        this.lhs.toArray(a);
        this.rhs.toArray(a);
        return a; }
    rerender(sub, app, vvar, nodecursor) {
        log('rerender', this.constructor.name, subToArray(sub));
        assert(nodecursor);
        sub = this.goal.apply(sub);
        if (sub.isFailure()) {
            this.remove();
            return [new FailureView(this), nodecursor]; }
        [this.lhs,nodecursor] = this.lhs.rerender(sub, app, vvar, nodecursor);
        [this.rhs,nodecursor] = this.rhs.rerender(sub, app, vvar, nodecursor);
        return [this, nodecursor];
    }
    items(a=[]) {
        this.lhs.items(a);
        this.rhs.items(a);
        return a; }
    firstNode() { return this.lhs.firstNode() ?? this.rhs.firstNode(); }
    lastNode() { return this.rhs.lastNode() ?? this.lhs.lastNode(); }
    asGoal() { return this.goal.conj(this.lhs.asGoal().disj(this.rhs.asGoal())); }
    toString() { return `(conde ${this.goal} ${this.lhs} ${this.rhs})`; }}

class FailView { // Failures on the initial render that may expand to leaves or branches.
    constructor(goal) {
        this.goal = goal; }
    items(a=[]) { return a; }
    firstNode() { return null; }
    lastNode() { return null; }
    remove() {}
    root(fragment=document.createDocumentFragment()) { return fragment; }
    rerender(sub, app, vvar, nodecursor) {
        log('rerender', this.constructor.name, subToArray(sub));
        assert(nodecursor);
        let expanded = this.goal.expand_run(sub, [vvar, app]);
        if (expanded instanceof this.constructor) return [expanded, nodecursor];
        nodecursor.after(expanded.root());
        return [expanded, expanded.lastNode()];
    }
    toString() { return `(fail ${this.goal})`; }}

class FailureView { // Rerender failures of atomic leaves that may cache nodes
    constructor(child) { //TODO can we remove failure views and just have the answers succeed or fail on their own?
        this.child = child; }
    items(a=[]) { return a; }
    firstNode() { return null; } // Prevents dynamic nodes from inserting anchors on a node not in the dom
    lastNode() { return null; }
    remove() {}
    rerender(sub, app, vvar, nodecursor) {
        log('rerender', this.constructor.name, subToArray(sub));
        let [c,nextcursor] = this.child.rerender(sub, app, vvar, nodecursor);
        if (c instanceof this.constructor) return [c, nodecursor];
        nodecursor.after(c.root()); // Normally items would not make changes to dom, so add in items that were previously removed.
        return [c, nextcursor]; 
    }
    root (fragment=document.createDocumentFragment()) { return fragment; }
    toString() { return `(fail ${this.child})`; }}

class AnswerView { // Displayable iterable item
    constructor(goal, template=null, child=null, order=null) {
        this.goal = goal;
        if (template instanceof LVar) throw Error(template);
        this.child = child;
        this.template = template;
        this.order = order; }
    static render(goal, sub, vvar, app, ovar) {
        assert(app instanceof RK)
        log('render', this.name, sub?.reify(vvar), vvar+'', goal+'', subToArray(sub));
        if (!sub) return new FailView(goal);
        let template = sub.walk(vvar);
        assert(!(template instanceof List), !(template instanceof LVar));
        return new this(goal, template, View.render(sub, app, template), ovar); }
    rerender(sub, app, vvar, nodecursor) {
        sub = this.goal.apply(sub);
        if (sub.isFailure()) {
            log('rerender', this.constructor.name, 'fail', vvar, subToArray(sub));
            this.remove();
            return [new FailureView(this), nodecursor]; }
        log('rerender', this.constructor.name, vvar, sub.walk(vvar), subToArray(sub));
        assert(!(sub.walk(vvar) instanceof List), !(sub.walk(vvar) instanceof LVar));
        this.child = this.child.rerender(sub, app, sub.walk(vvar));
        return [this, this.lastNode()];
    }
    root(fragment) {
        log('root', this.constructor.name, fragment);
        if (fragment) fragment.append(this.child.root());
        else return this.child.root(); }
    key() { return this.template; }
    remove() { this.child.remove(); }
    firstNode() { return this.child.firstNode(); }
    lastNode() { return this.child.lastNode(); }
    items(a=[]) {
        a.push(this);
        return a; }
    toArray(a) { a.push(this); return a; }
    toString() { return this.goal.toString(); }}


class NodeView { 
    constructor(template, children, node) {
        this.template = template;
        this.node = node;
        this.children = children; }

    static render(sub, app, template) {
        log('render', this.name, template, sub);
        let children = [];
        let node = this.render_node(template, sub, app, children);
        log('render', this.name + '^', children);
        return new this(template, children, node);
    }
    static render_node([tparent, ...tchildren], sub, app, children) {
        let parent = this.render_parent(tparent, sub, app, children);
        this.render_children(parent, [...tchildren], sub, app, children);
        return parent;
    }
    static render_parent(tparent, sub, app, children) {
        if (is_string(tparent)) return this.render_parent({tagName: tparent});
        if (tparent instanceof LVar) return this.render_parent(sub.walk(tparent), sub, children);
        let parent = document.createElement(tparent.tagName ?? 'div');
        for (let k in tparent) {
            log('render', 'attr', parent, k, tparent[k]);
            if (k === 'tagName') continue;
            else if (k.substr(0,2) === 'on') children.push(EventView.render(sub, parent, k.substr(2), Goal.as_goal(tparent[k]), app));
            this.render_property(tparent[k], parent, k, sub, app, children);
        }
        return parent;
    }
    static render_property(tproperty, parent, propname, sub, app, children) {
        if (is_text(tproperty)) parent[propname] = tproperty;
        else if (Array.isArray(tproperty) && tproperty.flat(Infinity).every(e => is_text(e))) {
            parent[propname] = tproperty.flat(Infinity).join(' '); }
        else if (tproperty instanceof LVar || tproperty instanceof Function) {
            children.push(AttrView.render(sub, parent, propname, tproperty)); }
        else {
            if (Object.values(tproperty).every(e => !e || e === true)) {
                parent[propname] = Object.entries(tproperty).filter(e => e[1]).map(e => e[0]).join(' '); }
            else {
                for (let k in tproperty) {
                    this.render_property(tproperty[k], parent[propname], k, sub, app, children); }}}}
    static render_children(parent, tchildren, sub, app, children) {
        log('render', this.name, 'children', parent, tchildren);
        for (let tchild of tchildren) {
            this.render_child(parent, tchild, sub, app, children); }
    }
    static render_child(parent, tchild, sub, app, children) {
        log('render', this.name, 'child', parent, tchild);
        if (is_text(tchild)) parent.append(tchild);
        else if (Array.isArray(tchild)) parent.append(this.render_node(tchild, sub, app, children));
        else {
            children.push(GoalView.render(sub, app, tchild));
            parent.append(children[children.length-1].root()); }}
    
    rerender(sub, app, template=this.template) {
        if (!equals(template, this.template)) {
            log('rerender', this.constructor.name, 'render', this.template, template);
            let v = View.render(sub, app, template); //TODO thread app
            this.node.replaceWith(v.root());
            return v; }
        log('rerender', this.constructor.name, template, this.template, equals(template, this.template), this.children, subToArray(sub));
        for (let i in this.children) this.children[i] = this.children[i].rerender(sub, app);
        return this;
    }
    root() { return this.node; }
    remove() { if (this.node) this.node.remove(); }
    firstNode() { return this.node; }
    lastNode() { return this.node; }}

class TextView {
    constructor(template, node) {
        this.template = template;
        this.node = node; }
    static render(template) {
        return new this(template, document.createTextNode(template));
    }
    rerender(sub, app, template=this.template) {
        log('rerender', this.constructor.name, template, this.template);
        if (is_text(template)) {
            if (this.template !== template) {
                this.template = template;
                this.node.textContent = template; }
            return this; }
        return View.render(sub, app, template); //TODO thread app
    }
    root() {
        log('root', this.constructor.name, this.template);
        assert(this.node.textContent === this.template);
        return this.node; }
    remove() { if (this.node) this.node.remove(); }
    firstNode() { return this.node; }
    lastNode() { return this.node; }}

class AttrView {
    constructor(node, attr, goal, vvar) {
        this.node = node;
        this.attr = attr; //TODO if attr is tagName, generate new node, swap children, and swap into dom
        this.goal = goal;
        this.vvar = vvar; }
    
    static render(sub, node, attr, val) {        
        log('render', this.name, subToArray(sub));
        if (val instanceof LVar) return this.render_lvar(sub, node, attr, val);
        else if (val instanceof Function) this.render_f(sub, node, attr, val, new LVar());
        else throw Error(val); }

    static render_lvar(sub, node, attr, val) { return new this(node, attr, succeed, val).rerender(sub); }
    
    static render_f(sub, node, attr, val, vvar) {
        return new this(node, attr, val(vvar), vvar).rerender(sub); }
    
    rerender(sub, app) {
        log('rerender', this.constructor.name, this.node, this.attr, sub.reify(this.vvar), this.vvar, subToArray(sub))
        let vals = this.goal.run(-1, {reify: this.vvar, substitution: sub});
        if (vals.isNil()) delete this.node[this.attr];
        else this.node[this.attr] = vals.join(' ');
        return this; }}

class EventView {
    constructor(sub) {
        this.substitution = sub; }
    
    static render(sub, node, event, handler, app) {
        let self = new this(sub); // Keep a reference to the view, which may mutate its sub.
        node.addEventListener(event, e =>
            app.update((handler instanceof Goal ? handler : Goal.as_goal(handler(e, e.target.value))).rediff(self.substitution)));
        return self; }
    
    rerender(sub) {
        this.substitution = sub;
        return this; }}

// Constants
const nil = new Empty();
const fail = new Fail();
const succeed = new Succeed();
const failure = new Failure();

export {RK, list, cons, eq, succeed, fail, fresh, conj, conde, LVar, MVar};

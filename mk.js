"use strict"
import {logging, log, dlog, toString, copy, equals, is_string, is_number, is_boolean} from './util.js';
//TODO let query variables be added manually not just extracted from fresh

// Lists
class List {
    static fromTree(a) {
        return list(...a).map(x => Array.isArray(x) ? this.fromTree(x) : x);
    }
    [Symbol.iterator]() {
        return this.toArray()[Symbol.iterator]();
    }
    length() {
        return this.toArray().length;
    }
    cons(e) {
        return new Pair(e, this);
    }
    acons(k, v) {
        return this.cons(new Pair(k, v));
    }
    extend(k, v) {
        return this.filter(x => x.car != k).acons(k, v);
    }
    member(e) {
        return this.memp((x) => x == e);
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
    walk(lvar) {
        if (!(lvar instanceof LVar)) return lvar;
        const v = this.assoc(lvar);
        if (v) { return this.walk(v.cdr); }
        else return lvar;
    }
    walk_binding(lvar) {
        if (!(lvar instanceof LVar)) return new Pair(lvar, lvar);
        const v = this.assoc(lvar);
        if (v) { return (v.cdr instanceof LVar) ? this.walk_binding(v.cdr) : v; }
        else return new Pair(lvar, lvar);
    }
    reify(lvar) {
        if (arguments.length == 0) return this.map((b) => new Pair(b.car, this.reify(b.cdr)));
        let v = this.walk(lvar);
        if (v instanceof LVar || primitive(v)) return v;
        if (v instanceof QuotedVar) return this.reify(v.lvar);
        if (v instanceof Pair) return new Pair(this.reify(v.car), this.reify(v.cdr));
        if (Array.isArray(v)) return v.map(e => this.reify(e));
        return Object.fromEntries(Object.entries(v).map(([k,v]) => [k, this.reify(v)]));
    }
    walk_path(lvar, prop, ...path) {
        let v = this.walk(lvar);
        if (path.length == 0) return v[prop];
        return this.walk_path(v[prop], ...path);
    }
    toString() {
        return '(' + this._toString() + ')';
    }
    unify(x_var, y_var) { //DOC unifier has to be very lazy about preserving variable paths and not updating to latest value
        let x, y;
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
        let s = this;
        for (let k of Object.keys(x).filter(k => Object.hasOwn(y, k))) {
            s = s.unify(x[k], y[k]);
            if (s.isFailure()) return failure;
        }
        return s;
    }
    update_binding(x, y, prev=nil, next=nil, updates=nil) {
        if (primitive(x)) return this;
        let {car: x_var, cdr: x_val} = prev.walk_binding(x);
        
        let {car: y_var, cdr: y_val} = prev.walk_binding(y);
        /*
        if (next.assoc(x_var)) {            
            y_val = next.assoc(x_var).cdr;
            log('reunify', 'subterm', x_var, y_val, next);
        }
        */
        log('reunify', 'lookup', x_var, x_val, y_var, y_val, prev);


        /*
        //if (next.assoc(y_var)) { //TODO need to walk repeatedly until exhausted
        let y_update = next.assoc(y_var);
        //log('reunify', 'occurs-check', 'x_var', x_var, 'y_var', y_var, 'y_update', y_update, 'occurs', occurs_check(x_var, y_var, prev), 'prev', prev);
        if (y_update && occurs_check(x_var, y_var, prev)) {
            log('reunify', 'occurs', 'x_var', x_var, 'y_var', y_var, 'y_val', y_val, 'y_update', y_update.cdr, 'curr', this, 'updates', updates);
            y_val = prev.walk(y_update.cdr);
            updates = updates.remove(y_update);
        }

        if (x_val instanceof QuotedVar && !(y_val instanceof QuotedVar)) {
            return this.update_binding(x_val.lvar, y_val, prev, next, updates);
        }
        */

        // Old prim values dont need to be reconciled, so just create new storage and update the new value.
        if (primitive(y_val) || y_val instanceof QuotedVar) {
            log('reunify', 'y prim', x_var, y_val);
            return updates.update_substitution(this.extend(x_var, y_val), prev, next); }

        else { // If old and new are objects, update the properties that exist and allocate new storage for those that don't.
            let norm = copy(y_val); //TODO should be type of y_val
            if (!primitive(x_val) && !(x_val instanceof LVar)) Object.assign(norm, x_val);
            
            for (let k in y_val) { // For each attr of the new value,                
                if (!primitive(x_val) && !(x_val instanceof LVar) && Object.hasOwn(x_val, k)) { // if it already exists in the target, merge those bindings.
                    //s = s.update_binding(x_val[k], y_val[k], prev, next);
                    updates = updates.acons(x_val[k], y_val[k]);
                }
                else { // Otherwise, allocate new memory for the new values.
                    norm[k] = new SVar();
                    updates = updates.acons(norm[k], y_val[k]);
                    //s = s.update_binding(norm[k], y_val[k], prev, next);
                }
            }
            log('reunify', 'complex', x_var, norm);
            return updates.update_substitution(this.extend(x_var, norm), prev, next); //TODO we dont have to extend if we don't add any properties
        }
    }
    equiv_svars(v) { // Find all svars that point to the same svar as v in this substitution.
        let equiv = this.filter(b => b.cdr === v).map(b => this.equiv_svars(b.car)).fold((x,y) => x.append(y), nil)
        if (v instanceof SVar) return equiv.cons(v);
        return equiv;
    }
}

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
    assoc(key) {
        if (this.car instanceof Pair && this.car.car == key) {
            return this.car;
        }
        else {
            return this.cdr.assoc(key);
        }
    }
    memp(p) {
        if (p(this.car)) return this.car;
        return this.cdr.memp(p);
    }
    filter(p) {
        if (p(this.car)) return this.cdr.filter(p).cons(this.car);
        return this.cdr.filter(p);
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
    update_substitution(curr, prev=curr, next=this) { // Called on the updates substitution with the normal substitution as a parameter.
        return curr.update_binding(this.caar(), this.cdar(), prev, next, this.cdr);
    }
    every(f) {
        f(this.car);
        this.cdr.every(f);
        return this; }
    isNil() { return false; }

    // x->1, y->2     

    
    _toString() {
        return `${toString(this.car)}${this.cdr instanceof Pair ? ' ' : ''}${this.cdr instanceof List ? this.cdr._toString() : ' . ' + toString(this.cdr)}`;
    }
}

class Empty extends List {
    toArray() {
        return [];
    }

    assoc(key) {
        return false;
    }
    memp(p) { return undefined; };
    filter(p) { return this; };
    map(f) { return this; };
    update_substitution(s) { return s; }
    append(xs) { return xs; }
    isNil() { return true; }
    fold(f, x) { return x; }
    remove(x) { return this; }
    every(f) { return this; }
    _toString() { return ''; }
}

function cons(...xs) { return xs.reduceRight((x,y) => new Pair(y, x)); }

function list(...xs) { return cons(...xs, nil); }

// Vars & Data
class LVar {
    static id = 0;
    constructor() {
	this.id = LVar.id++;
        this.label = '';
    }
    toString() {
        return `<${this.label}${this.label ? ':' : ''}${this.id}>`;
    }
    unify(x) {
        return new Unification(this, x);
    }
    eq(x) { return this.unify(i); }
    eq(x) { return this.unify(x); }
    set(x) { return new Reunification(this, x); }
    name(n) { this.label = n; return this; }
    quote() { return new QuotedVar(this); }
    constraint(f, ...lvars) { return new Constraint(f, this, ...lvars); }
    isStringo() { return this.constraint(v => is_string(v)); }
    isNumbero() { return this.constraint(v => is_number(v)); }
    isPairo() { return this.constraint(v => v instanceof Pair); }
    membero(x) { return fresh((a,b) => [this.eq(cons(a,b)), conde(a.eq(x), b.membero(x))]); }
}

class SVar extends LVar {
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
    conj(x) {
        if (succeed === x) return this;
        if (fail === x) return fail;
        return new Conj(this, x);
    }
    disj(x) {
        if (fail === x) return this;
        return new Disj(this, x);
    }
    filter(f) { return f(this) ? this : succeed; }
    run(n=-1, {reify=true, substitution=nil}={}) {
        return this.eval(new State(substitution)).take(n).map(s => reify ? s.reify(nil) : s);

    }
    expand_run(s=nil, v=((g,s) => s ? ViewLeaf.render_template(g, s, v, null) : new ViewStump(g))) { //TODO remove default viewleaf
        return this.expand(new State(s), succeed, succeed, v);
    }
    reunify_substitution(sub) {
        let r = this.run(-1, {reify: false, substitution: sub});
        let updates = r.map(st => st.reify_updates()).fold((ups, up) => up.append(ups), nil); //TODO may need to walk_binding the reunifications so theyre not dependent on transient state that will be thrown away. also, what happens if setting free vars?
        log('reunify', 'updates', updates, sub);
        return updates.update_substitution(sub);
    }
    cont(s) { return s.isFailure() ? failure : this.eval(s); }
    expand_ctn(s, cjs, v) {
        log('expand', 'ctn', this, cjs, s);
        return s.isFailure() ? v(cjs.conj(this)) : this.expand(s, succeed, cjs, v); }
    suspend(s) { return new Suspended(s, this) }
    is_disj() { return false; }
    toString() { return JSON.stringify(this); }
}

class Succeed extends Goal {
    eval(s) { return s; }
    suspend(s, ctn=succeed) { return ctn.cont(s); }
    cont(s) { return s; }
    expand_ctn(s, cjs, v) {
        log('expand', 'return', this, cjs, s);
        //return new ViewLeaf(g, s.reify(v));
        return v(cjs,s);
    }
    conj(g) { return g; }
    expand(s, ctn, cjs, v) { return s.expand_ctn(ctn, cjs, v); }
    toString() { return 'succeed'; }
}

class Fail extends Goal {
    eval(s) { return failure; }
    suspend(s) { return failure; }
    conj(g) { return fail; }
    expand(s, ctn, cjs, v) {
        log('expand', 'fail', cjs.conj(ctn));
        return v(cjs.conj(ctn)); }
    toString() { return 'fail'; }
}

class Conj extends Goal {
    constructor(lhs, rhs) {
        super();
        if (!lhs || !rhs) throw new Error('Conj takes 2 arguments' + lhs + rhs);
        this.lhs = lhs;
        this.rhs = rhs;
    }
    filter(f) { return this.lhs.filter(f).conj(this.rhs.filter(f)); }
    eval(s, ctn=succeed) {
        return this.lhs.eval(s, this.rhs.conj(ctn));
    }
    expand(s, ctn, cjs, v) {
        log('expand', 'conj', this, ctn, cjs);        
        return this.lhs.expand(s, ctn.conj(this.rhs), cjs, v); 
    }
    toString() { return `(${this.lhs} & ${this.rhs})`; }
}

class Disj extends Goal {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    is_disj() { return true; }
    eval(s, ctn=succeed) {
        return this.lhs.eval(s, ctn).mplus(this.rhs.eval(s, ctn));
    }
    expand(s, ctn, cjs, v) {
        log('expand', 'disj', this, ctn, cjs);
        return new IterableViewBranch(cjs, this.lhs.expand(s, ctn, succeed, v), this.rhs.expand(s, ctn, succeed, v));
    }
    toString() { return `(${this.lhs} | ${this.rhs})`; }
}

class Fresh extends Goal {
    constructor(vars, ctn) {
        super();
        this.vars = vars;
        this.ctn = ctn;
    }
    run(n=-1, {reify=true, substitution=nil}={}) {
        return this.eval(new State(substitution)).take(n).map(s => reify ? log('run', 'reify', s.substitution.reify(this.vars)) : s);
    }
    eval(s, ctn=succeed) {
        return this.instantiate().conj(ctn).suspend(s);
    }
    expand(s, ctn, cjs, v) {
        return this.instantiate().expand(s, ctn, cjs, v);
    }
    instantiate() { return to_goal(this.ctn(...this.vars)); }
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
        log('expand', '==', this, ctn, cjs);
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
    expand(s, ctn, cjs, v) {
        log('expand', 'constraint', this, ctn, cjs);
        s = (this.f.apply(null, this.lvars.map(x => s.walk(x)))) ? s : failure;
        return s.expand_ctn(ctn, cjs.conj(this), v);
    }
    toString() { return `${this.f}(${this.lvars})`; }
}

class Reunification extends Goal {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    toString() { return `(${toString(this.lhs)} =!= ${toString(this.rhs)})`; }
    eval(s, ctn=succeed) { return ctn.cont(s.update(this.lhs, this.rhs)); }
}

function conde(...condes) {
    return condes.reduceRight((cs, c) => to_goal(c).disj(cs), fail);
}

function conj(...conjs) {
    return conjs.reduceRight((cs, c) => to_goal(c).conj(cs), succeed);
}

function unify(x, y) {
    return new Unification(x, y);
}

function reunify(x, y) {
    return new Reunification(x, y);
}

function to_goal(g) {
    if (Array.isArray(g)) return g.reduceRight((cs, c) => to_goal(c).conj(to_goal(cs)));
    else if (true === g) return succeed;
    else if (false === g) return fail;
    else return g;
}

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
    expand_ctn(ctn, cjs, rtrn) { return rtrn(cjs.conj(ctn)); }
}

class State extends Stream {
    constructor(sub=nil, updates=nil) {
        super();
        this.substitution = sub;
        this.updates = updates;
    }
    take(n) { return list(this); }
    reify(x) { return this.substitution.reify(x); }
    unify(x, y) {
        let s = this.substitution.unify(x, y);
        log('unify', x, y, this.substitution, '->', s);
        if (s == failure) return s;
        return new State(s, this.updates); }
    reify_updates() {
        return this.updates.map(u =>
            this.substitution.equiv_svars(this.walk_binding(u.car).car).map(v => cons(v, this.reify_update(u.cdr, this.walk_binding(u.car).car))))
            .fold((x,y) => x.append(y), nil); }
    reify_update(lvar, parent) {
        let {car: vr, cdr: v} = this.substitution.walk_binding(lvar);
        log('reunify', 'skipreify', parent, lvar, vr, v);
        if (vr != parent && occurs_check(parent, vr, this.substitution) && this.updates.assoc(vr)) {
            return this.reify_update(this.updates.assoc(vr).cdr, parent);
        }
        if (v instanceof LVar || primitive(v)) return v;
        if (v instanceof QuotedVar) return this.reify(v.lvar);
        if (v instanceof Pair) return new Pair(this.reify(v.car), this.reify(v.cdr));
        if (Array.isArray(v)) return v.map(e => this.reify(e));
        return Object.fromEntries(Object.entries(v).map(([k,v]) => [k, this.reify(v)]));
    }
    update(x, y) {
        return new State(this.substitution, this.updates.acons(x, y)); }
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


function descendant_order(x,y,s) { // Descendants go first, so -1 if x is a descendant of y
    if (occurs_check(y, x, s)) return -1; //TODO delete fn
    else if (occurs_check(x, y, s)) return 1;
    return 0;
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

// Constants
const nil = new Empty();
const fail = new Fail;
const succeed = new Succeed;
const failure = new Failure;

// DOM

function render(tmpl, sub=nil, model=null) {
    log('render', tmpl);
    if (is_string(tmpl) || is_number(tmpl)) { // Simple Text nodes
        return new ViewTextNode(tmpl);
	//let node = document.createTextNode(tmpl);
        //log('render', 'text', tmpl, node);
	//return [node, []];
    }
    /*
    else if (tmpl instanceof LVar) { // Build a dynamic node keyed to a single static model var
        log('render', 'var', tmpl);
        return DynamicNode.render(tmpl, sub, obs, model, update, goals); }*/
    else if (tmpl instanceof Function) { // Build a dynamic node using the model
        let v = new LVar();
        let g = tmpl(v, model);
        log('render', 'fn', g);
        if (g instanceof Goal) { // Must be a template because no templates supplied for leaf nodes
            let o = g.expand_run(sub, (g, s) => s ? ViewLeaf.render_template(g, s, v, model) : new ViewStump(g));
            //return [o.render(sub, model, v), new IterableViewRoot(v, o)];
            return new IterableViewRoot(v,o);

        }
        else { return render(g, sub, model); }
    }
    //else if (tmpl instanceof LVar) { return render(sub.walk(tmpl), sub, model); }
    else if (Array.isArray(tmpl)) return render_head(tmpl, sub, model);
    else {
        console.error('Unrecognized render template', tmpl); //TODO remove debug print when done developing
        throw Error('Unrecognized render template: ' + toString(tmpl)); }}

function render_head([tmpl_head, ...tmpl_children], sub, model) {
    log('render', 'head', tmpl_head, tmpl_children);
    if (is_string(tmpl_head)) {
        let parent = new ViewDOMNode(tmpl_head, tmpl_children.map(c => render(c, sub, model)));
        /*
        for (let c of tmpl_children) {
            let [n,o] = render(c, sub, model);
            parent.appendChild(n);
        }*/
        //return [parent, []];
        return parent;
    }
    else if (tmpl_head instanceof Function) {
        let v = new LVar();
        let g = tmpl_head(v, model);
        let o = g.expand_run(sub, (g,s) => render(tmpl_children[0], s, v));
        return new SubView(v, o);
        //return [o.render(sub, v, [...tmpl_children]), ]

        ;
    }
    else {
        console.error('Unrecognized render head template', tmpl_head); //TODO remove debug print when done developing
        throw Error('Unrecognized render head template: ' + toString(tmpl_head)); }
}



class View {
    update(s) {
        return this.rerender(s);
        //return this;
    }
    prerender() {
        log('render', 'prerender');
        this.render();
        return this; }
    isFailure() { return false; }
}

class IterableViewRoot extends View { //Replaces a child template and generates one sibling node per answer, with templates bound to the view var. 
    constructor(viewvar, child, comment=document.createComment('')) {
        super();
        this.lvar = viewvar;
        this.child = child; //Root of tree of views.
        this.comment = comment;
    }
    rerender(sub, model) {
        // walk existing tree, generating new nodes by manually running goals on substitution. pass off nodes as we go
        // iterableview is responsible for deletions. it scans children and if all fail, insert comment ahead of first child
        // with comment inserted as needed, remove all failing nodes with another pass and insert new nodes (get an array of children so we can do ordering)
        // at fail leaves we re-evaluate the goal 
        // generate new child tree
        // tandem walk trees and hand off nodes
        // if all leaves fail in 
        // if no  passing leaves, 
        // get list of child leaves from both trees
        // if all fail, and we are not failing, we fail and insert a comment & remove everything
        // if all fail and we are already failing, do nothing

        // we cant naively generate a new tree bc we'd rebuild all the dom nodes, and we cant easily generate a pure value tree bc
        log('render', 'rerender', 'iterviewroot');
        let updates = [];
        let r = new IterableViewRoot(this.lvar, this.child.rerender(sub, model, this.lvar, updates), this.comment);
        log('render', 'rerender', 'iterroot', 'updates', updates);
        updates.reduce((n,c) => c.t1.replaceDOM(c.t0, n), this.comment);
        
        // get first attached child (comment or first non fail with parent
        // if no children attached, no edits needed
        // if it is the comment node, start the insert-after process, inserting and removing as needed
        //let firstAttachedChild = updates.find(t => !t.isFailure());
        return r; }
    render(parent) {
        if (parent) parent.appendChild(this.comment);
        return this.child.render(parent); }
    remove() { this.child.remove(); }
    lastNode() { this.child.lastNode(); }}

class SubView extends View {
    constructor(lvar, child) {
        super();
        this.lvar = lvar;
        this.child = child; }
    update(sub) {
        throw Error('nyi')
        this.child.update(sub, this.lvar); }
    render(parent) {
        return this.child.render(parent); }
    remove() { this.child.remove(); }}

class ViewStump extends View {
    constructor(goal) {
        super();
        this.goal = goal; }
    render(parent) {
        log('render', 'stump');
        if (!parent) return document.createDocumentFragment(); } //TODO make a global empty doc frag
    rerender(sub, lvar) {
        throw Error('NYI')
    }
    replaceDOM(view0, node) {
        view0.remove();
        return node; }
    harvest(tree) { tree.remove(); }
    isFailure() { return true; }
    remove() {}
    asGoal() { return this.goal; }}

class ViewDOMNode extends View {
    constructor(properties, children=[], node=null) {
        super();
        this.properties = properties;
        this.node = node;
        this.children = children; }
    render(parent) {
        log('render', 'dom', this.node);
        if (this.node) return this.node;
        console.assert(is_string(this.properties));
        this.node = document.createElement(this.properties);
        if (parent) parent.appendChild(this.node);
        this.children.forEach(c => c.render(this.node));
        return this.node; }
    rerender(sub, vvar, model) {
        return new ViewDOMNode(this.properties, this.children.map(c => c.rerender(sub, vvar, model)), this.node);
    }
    remove() { if (this.node) this.node.remove(); }
    lastNode() { this.children.at(-1).lastNode(); }}

class ViewTextNode extends View {
    constructor(text) {
        super();
        this.text = text;
        this.node = null; }
    render(parent) {
        this.node = document.createTextNode(this.text);
        if (parent) parent.appendChild(this.node);
        return this.node; }
    rerender(sub, vvar, model) { return this; }
    remove() { if (this.node) this.node.remove(); }
    lastNode() { this.node; }}

class ViewLeaf extends ViewStump {
    constructor(goal, template, child) {
        super(goal);
        this.template = template;
        this.child = child;
        //let [n,o] = render(sub.reify(view), sub, model);
        //this.cache = sub.reify(view);
        //this.children = o;
        //this.node = n;
    }
    static render_template(goal, sub, lvar, model) {
        let tmpl = sub.reify(lvar);
        log('render', 'iteritem', tmpl, sub);
        if (tmpl instanceof LVar) throw Error('Iterable templates must not be free');
        return new this(goal, tmpl, render(tmpl, sub, model));
    }
    render(parent) {
        log('render', 'leaf', this.cache);
        //let [n, o] = render(this.cache, sub, model);
        //return this.node;
        return this.child.render(parent);
    }
    subview(sub, model, templates) {
        let [n,o] = render(templates[0], sub, model);
    }
    update2(sub, lvar) {
        throw Error('nyi')
        return this.goal.expand_run(sub, lvar).harvest(this); }
    rerender(sub, model, vvar, updates) {        
        let t1, states = this.goal.run(1, {reify: false, substitution: sub});
        log('render', 'rerender', 'iteritem', 'goal', this.goal);
        if (states.isNil()) t1 = new ViewStump(this.goal);
        else {
            sub = states.car.substitution;
            let tmpl = sub.reify(vvar);
            if (!equals(tmpl,this.template)) t1 = new ViewLeaf(this.goal, tmpl, render(tmpl, sub, model));
            else t1 = new ViewLeaf(this.goal, this.template, this.child.rerender(sub, lvar, model)); }
        log('render', 'rerender', 'iteritem', 'update', t1);
        updates.push({t0: this, t1: t1});
        return t1;
    }
    remove() { this.child.remove(); }
    lastNode() { this.child.lastNode(); }
    replaceDOM(view0, node) { // TODO no-op if templates are equal
        node.after(this.render());
        view0.remove();
        return this.lastNode();
    }
    harvest(tree) {
        this.node = tree.node;
        this.node.textContent = this.cache; }}

class IterableViewBranch extends View {
    constructor(goal, lhs, rhs) {
        super();
        this.goal = goal;
        this.lhs = lhs;
        this.rhs = rhs;
    }
    render(parent=document.createDocumentFragment()) {
        log('render', 'branch', this.lhs, this.rhs);
        this.lhs.render(parent);
        this.rhs.render(parent);
        return parent; }
    update(sub, lvar) {
        throw Error('NYI')
    }
    remove() {
        this.lhs.remove();
        this.rhs.remove(); }
    lastNode() { this.rhs.lastNode(); }
    asGoal() { return this.goal.conj(this.lhs.asGoal().disj(this.rhs.asGoal())); }
}

export {nil, cons, list, List, Pair, LVar, primitive, succeed, fail, fresh, conde, unify, reunify, failure, Goal, quote, QuotedVar, conj, SVar, render};

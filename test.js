let logging = false;
function log(...args) {
    if (logging) console.log.apply(console, args);
    return args.length == 1 ? args[0] : args;
}

function test(f, test_name) {
    try {
	f();
    } catch (x) {
	document.write('error in test: ' + (test_name || 'Unnamed'));
	throw x;
    }
}

function assert(a, ...debug_info) {
    if (!a) {
	console.log(...debug_info);
	throw Error("Assertion failed");
    }
}

function equals(a, b) {
    return JSON.stringify(a) == JSON.stringify(b);
}

function asserte(a, b) {
    if (!equals(a, b)) throw Error(JSON.stringify(a) + ' != ' + JSON.stringify(b));
}

function primitive(x) {
    return typeof x == 'string' || typeof x == 'number' || x instanceof Empty || x === null || x === undefined;
}

class LVar {
    static id = 0;
    constructor() {
	this.id = LVar.id++;
    }
    toString() {
        return '<' + this.id + '>';
    }
    unify(x) {
        return new Unify(this, x);
    }
}

class Goal {
    conj(x) {
        return new Conj(this, x);
    }
    disj(x) {
        return new Disj(this, x);
    }
    run(n) {
        return this.eval(new State()).take(n).map(s => s.reify(nil));
        
    }
    suspend(s) { return new Suspended(s, this) }
}

class Succeed extends Goal {
    eval(s) { return s }
    suspend(s) { return s }
}
var succeed = new Succeed;

class Fail extends Goal {
    eval(s) { return failure }
    suspend(s) { return failure }
}
var fail = new Fail;

class Conj extends Goal {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    eval(s) {
        return this.rhs.eval(this.lhs.eval(s));
    }
}

class Disj extends Goal {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    eval(s) {
        return this.lhs.eval(s).mplus(this.rhs.eval(s));
    }
}

class Fresh extends Goal {
    constructor(vars, ctn) {
        super();
        this.vars = vars;
        this.ctn = ctn;
    }
    run(n=1) {
        return this.eval(new State()).take(n).map(s => s.reify(this.vars));        
    }
    eval(s) {
        return to_goal(this.ctn(...this.vars)).suspend(s);
    }
}

class Unify extends Goal {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    eval(s) {
        return s.unify(this.lhs, this.rhs);
    }
}

class Stream {
    mplus(s) { return s._mplus(this) }
    _mplus(s) { return new MPlus(this, s) }
    take(n) {
        let s = this;
        while (s.isIncomplete()) { s = s.step() }
        if (failure == s) return nil;
        return new Pair(s.answer(), s.step().take(n-1));
    }
    isIncomplete() { return true }
}

class Failure extends Stream {
    unify() { return this };
    reify(x) { return x };
    eval(x) { return this };
    mplus(s) { return s };
    _mplus(s) { return s };
    isIncomplete() { return false }
    step() { return this }
}
var failure = new Failure;

class State extends Stream {
    constructor(sub=nil, updates=nil) {
        super();
        this.substitution = sub;
        this.updates = updates;
    }
    take(n) { return List.from(this) }
    reify(x) { return this.substitution.reify(x) }
    unify(x, y) {
        let s = this.substitution.unify(x, y);
        if (s == failure) return s;
        return new State(s, this.updates) }
    update(x, y) {
        let s = this.updates.unify(x, y);
        if (s == failure) return s;
        return new State(this.substitution, s) }
    eval(g) { return g.eval(this) }
    isIncomplete() { return false }
    answer() { return this }
    step() { return failure }
    mplus(s) { return new Answers(this, s) }
    _mplus(s) { return new Answers(this, s) }
    update_substitution() { return this.updates.update_substitution(this.substitution) }
}

class Suspended extends Stream {
    constructor(s, g) {
        super();
        this.state=s;
        this.goal = g;
    }
    step() { return this.goal.eval(this.state) }
}

class Answers extends Stream {
    constructor(state, stream) {
        super();
        this.state = state;
        this.stream = stream;
    }
    isIncomplete() { return false }
    answer() { return this.state }
    step() { return this.stream }
    mplus(s) { return new Answers(this.state, this.stream.mplus(s)) }
    _mplus(s) { return new Answers(this.state, this.stream.mplus(s)) }
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

class UnifyUpdate extends Goal {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    eval(s) { return s.update(this.lhs, this.rhs) }
}

function to_goal(g) {
    return (Array.isArray(g)) ? g.reduceRight((cs, c) => c.conj(cs)) : g;
}

function conde(...condes) {
    return condes.reduceRight((cs, c) => to_goal(c).disj(cs));
}

function unify(x, y) {
    return new Unify(x, y);
}

function setunify(x, y) {
    return new UnifyUpdate(x, y);
}






// RRP
class PropObserver {
    constructor(lvar, node, attr) {
        this.lvar = lvar;
	this.node = node;
	this.attr = attr;
    }

    update(val) {
	this.node[this.attr] = val;
        return true;
    }
}

class IterObserver {
    constructor(lvar, node) {
        this.lvar = lvar;
	this.node = node;
    }

    update(val) {
        if (val instanceof Pair) return true;
        this.node.remove();
        return false;
    }
}

class List {
    static fromArray(a) {
        let l = nil;
        for (const e of a.reverse()) {
            l = l.cons(e);
        }
        return l;
    }
    static fromTree(a) {
        return this.fromArray(a).map(x => Array.isArray(x) ? this.fromTree(x) : x);
    }
    static from(...e) {
        return this.fromArray([...e]);
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
    member(e) {
        return this.memp((x) => x == e);
    }
    static repeat(n, f) {
        return nil.repeat(n, f);
    }
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
        if (v instanceof Pair) return new Pair(this.reify(v.car), this.reify(v.cdr));
        return Object.fromEntries(Object.entries(v).map(([k,v]) => [k, this.reify(v)]));
    }
    walk_path(lvar, prop, ...path) {
        let v = this.walk(lvar);
        if (path.length == 0) return v[prop];
        return this.walk_path(v[prop], ...path);
    }
    toString() {
        return '(' + this.toArray().join(' ') + ')';
    }
    unify(x, y) {
        x = this.walk(x);
        y = this.walk(y);
        if (x == y) return this;
        if (x instanceof LVar) return this.acons(x, y);
        if (y instanceof LVar) return this.acons(y, x);
        if (primitive(x) || primitive(y)) return failure;
        let s = this;
        for (let k of Object.keys(x).filter(k => Object.hasOwn(y, k))) {
            s = s.unify(x[k], y[k]);
            if (s === failure) return failure;
        }
        return s;
    }
}

class Pair extends List {
    constructor(car, cdr) {
	super();
	this.car = car;
	this.cdr = cdr;
    }
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
    map(f) {
        return this.cdr.map(f).cons(f(this.car));
    }
    update_substitution(s) { // Called on the updates substitution with the normal substitution as a parameter.
        let b = s.walk_binding(this.car);
        return s.acons(b.car, this.cdr);
    }
}

class Empty extends List {
    toArray() {
        return [];
    }
    
    assoc(key) {
        return false;
    }
    memp(p) { return undefined };
    filter(p) { return this };
    map(f) { return this };
    update_substitution(s) { return s }
}

const nil = new Empty();

// MK

function fresh(f) {
    return new Fresh(List.repeat(f.length, () => new LVar()), f);
}


// RRP

function normalize(model, substitution=nil) {
    log('normalize', model, substitution);
    if (model instanceof LVar) {
	return [model, substitution];
    }
    else if (Array.isArray(model)) {
	let tail = new LVar();
        substitution = substitution.acons(tail, nil);
	for (let i=model.length-1; 0<=i; i--) {            
            var [lvar, substitution] = normalize(model[i], substitution);
	    let tail2 = new LVar();
            substitution = substitution.acons(tail2, new Pair(lvar, tail));
            tail = tail2;
	}
	return [tail, substitution];
    }
    else if (typeof model == 'object') {
	let m = {};
	for (const k in model) {
	    //log('k',k,'submodel',model[k], 'substitution',JSON.stringify(substitution));
            var [lvar, substitution] = normalize(model[k], substitution);
            const lvar2 = new LVar();
            substitution = substitution.acons(lvar2, lvar);
	    m[k] = lvar2;
            //substitution = substitution.push(new LVar(substitution.push(lvar) - 1)) - 1
	    //log('id',m[k],'substitution',JSON.stringify(substitution));
	}
        const mvar = new LVar();
	return [mvar, substitution.acons(mvar, m)];
    }
    else {
        const lvar = new LVar();
	return [lvar, substitution.acons(lvar, model)];
    }
}


// RENDERING

function render(spec, sub=nil, obs=nil, model={}) {
    log('render', spec, sub, obs, model);
    if (typeof spec == 'string' || typeof spec == 'number') { // Simple Text nodes
	let node = document.createTextNode(spec);
	//return [node, new PropObserver(node, 'textContent')];
	return [node, sub, obs];
    }
    else if (spec instanceof Function) {
        return render(spec(model), sub, obs, model);
    }
    else if (Array.isArray(spec)) { // Build a DOM node
        let head_spec = sub.walk(spec[0]);
        if (head_spec instanceof List) { // Build an iterable DOM list
            let parent = document.createDocumentFragment();
            let items = head_spec;
            let linkvar = spec[0];
            
            while (items instanceof Pair) { //TODO deal with lvar tailed improper lists
                var [node, sub, obs] = render(spec[1], sub, obs, items.car);
                parent.appendChild(node);
                obs = obs.cons(new IterObserver(linkvar, node));
                linkvar = items.cdr;
                items = sub.walk(linkvar);
            }
            return [parent, sub, obs];
        } // Build a head node for the rest of the child specs
        else if (typeof head_spec == 'string'){
	    let parent = document.createElement(head_spec);
	    for (let i=1; i<spec.length; i++) {
	        log('child render', render(spec[i], sub, obs, model));
                var [node, sub, obs] = render(spec[i], sub, obs, model);
                parent.appendChild(node);
	    }
	    return [parent, sub, obs];
        }
        else throw Error('Unrecognized render spec head: ' + JSON.stringify(head_spec));
    }
    else if (spec instanceof LVar) { // Build a watched Text node
	var [node, sub, obs] = render(sub.walk(spec), sub, obs, model);
	return [node, sub, obs.cons(new PropObserver(spec, node, 'textContent'))];
    }
    else throw Error('Unrecognized render spec: ' + JSON.stringify(spec));
    //    		typeof child === 'number') head.appendChild(document.createTextNode(child));
    //document.createDocumentFragment());}
}

// UPDATING

function update(sub, obs) {
    return obs.filter((o) => o.update(sub.walk(o.lvar)));
}

function garbage_collect(sub, root) {
    return garbage_sweep(sub, garbage_mark(sub, root));
}

function garbage_mark(sub, root, marked=nil) {
    // Return vars in sub still reachable from root.
    if (root instanceof LVar) {
        if (marked.member(root)) return marked;
        return garbage_mark(sub, sub.assoc(root), marked.cons(root));
    }
    else if (primitive(root)) {
        return marked;
    }
    else {
        for (const p in root) {
            marked = garbage_mark(sub, root[p], marked);
        }
        return marked;
    }
}

function garbage_sweep(sub, marked) {
    return sub.filter((b) => marked.member(b.car));
}

// TESTING

logging=false;


let [m, s] = normalize({
    a: 1,
    b: 2,
    c: [3, 4],
    d: {e: 5, f: 6}
}, nil);

log("model",m);
log("substitution",s);

//Model
assert(s.walk(m).a instanceof LVar, s.walk(m).a);
asserte(garbage_mark(s, m).length(), 17);
asserte(garbage_mark(s.acons(s.walk_path(m, 'c'), s.walk_path(m,'a')), m).length(), 12);
asserte(garbage_sweep(s, garbage_mark(s.acons(s.walk_path(m, 'c'), s.walk_path(m,'a')), m)).length(), 12);

//Template
asserte(render(s.walk(m).a, s, nil, m)[0].textContent, '1');

//DOM

var o = nil; // observers: convert substitution values into dom updates

// Static
asserte(render('lorem', s, o, m)[0].textContent, 'lorem'); // Static text node
asserte(render(['div', 'lorem'], s, o, m)[0].innerHTML, 'lorem'); // Static dom node
asserte(render(['div', ['div', 'lorem']], s, o, m)[0].childNodes[0].innerHTML, 'lorem'); // Static nested dom node

// Dynamic
var [n,,o] = render(s.walk(m).a, s, o, m);
asserte(n.textContent, '1');
update(s.acons(s.walk(m).a, 2), o);
asserte(n.textContent, '2');

// Lists
asserte(render([List.fromArray(['ipsum', 'dolor']), ['div', 'lorem']], s, o, m)[0].childNodes[0].innerHTML, 'lorem');
asserte(render([List.fromArray(['ipsum', 'dolor']), ['div', function (e) { return 'lorem' }]], s, o, m)[0].childNodes[0].innerHTML, 'lorem');
asserte(render([List.fromArray(['ipsum', 'dolor']), ['div', function (e) { return e }]], s, o, m)[0].childNodes[0].innerHTML, 'ipsum');

// TDList
var [td_model, td_sub] =
    normalize({todos: [{title: 'get tds displaying', done: false},
                       {title: 'streamline api', done: false}]});

//console.log(td_sub + '')

var [td_node, td_sub, td_obs] =
    render(['div',
            [td_sub.walk(td_model).todos,
             ['div', function (e) {return td_sub.walk_path(e, 'title')}]]],
           td_sub, nil, td_model);
asserte(td_node.childNodes.length, 2);



/*
console.log(td_sub + '')
console.log(td_sub.reify() + '')
console.log(td_obs.map((x) => x.lvar) + '')
console.log(td_sub.walk_path(td_model, 'tds', 'cdr'))
console.log(td_sub.walk_path(td_model, 'tds', 'cdr', 'cdr'))
console.log(garbage_collect(
    td_sub.acons(td_sub.walk_path(td_model, 'tds', 'cdr'),
                   td_sub.walk_path(td_model, 'tds', 'cdr', 'cdr')), td_model) + '');
*/
//console.log(td_sub.reify(td_sub.walk(td_model).tds) + '')
//console.log(td_sub.acons(td_sub.walk_path(td_model, 'tds', 'cdr'),
//                           td_sub.walk(td_sub.walk_path(td_model, 'tds', 'cdr', 'cdr'))) + '');
td_sub = garbage_collect(
    td_sub.acons(td_sub.walk_path(td_model, 'todos', 'cdr'),
                   td_sub.walk_path(td_model, 'todos', 'cdr', 'cdr')), td_model)
//console.log(td_sub + '')
td_obs = update(td_sub, td_obs);
asserte(td_node.childNodes.length, 1);


//0: (cons #1 #2)
//1: 'test
//2: (cons #3 #4)
//3 'test2
//4 nil

//tail deletion
//0: (cons #1 #2)
//1: 'test
//2: #4            (cons #3 #4)
//3 'test2
//4 nil

//head deletion
//0: #2              (cons #1 #2)
//1: 'test
//2: (cons #3 #4)
//3 'test2
//4 nil

//multi deletion
//0: #4              (cons #1 #2)
//1: 'test
//2: (cons #3 #4)
//3 'test2
//4 nil

//multi deletion
//0: #4              (cons #1 #2)
//1: 'test
//2: (cons #3 #4)
//3 'test2
//4 nil

//insertion
//0: (cons #1 #2)
//1: 'test
//2: (cons #6 #7)          #3
//3: (cons #4 #5)
//4 'test2
//5 nil
//6 'test3
//7 #3

//first garbage collect all unreachable items
//if a list observer is changed to something other than original object, particularly a free var, delete its node
//console.log(td_sub)


// MK TEST

asserte((new Succeed).run(), List.from(nil));
asserte(fresh((x) => unify(x, 1)).run(), List.fromTree([[1]]));
asserte(fresh((x, y) => [x.unify(1), y.unify(2)]).run(), List.fromTree([[1, 2]]));
asserte(fresh((x) => [x.unify(1), x.unify(2)]).run(), nil);
asserte(fresh((x, y) => unify(new Pair(x,y), new Pair(1,2))).run(), List.fromTree([[1, 2]]));
asserte(fresh((x, y) => unify({a:x, b:y}, {a:1, b:2})).run(), List.fromTree([[1, 2]]));
asserte(fresh((x) => unify({a:1, b:x}, {a:1, b:2})).run(), List.fromTree([[2]]));
asserte(fresh((x) => unify({b:x}, {a:1, b:2})).run(), List.fromTree([[2]]));
asserte(fresh((x) => unify({a:1, b:2}, {b:x})).run(), List.fromTree([[2]]));
asserte(fresh((x) => conde(x.unify(1), x.unify(2))).run(2), List.fromTree([[1], [2]]));

document.body.appendChild(td_node);

console.log('Tests Complete');

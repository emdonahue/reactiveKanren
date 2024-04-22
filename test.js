let logging = false;
function log() {
    if (logging) console.log.apply(console, arguments);
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


class LVar {
    constructor(id) {
	this.id = id;
    }
}

class PropObserver {
    constructor(lvar, node, attr) {
        this.lvar = lvar;
	this.node = node;
	this.attr = attr;
    }

    update(val) {
	this.node[this.attr] = val;
    }
}

class List {
    static fromArray(a) {
        let l = nil;
        for (const e of a.reverse()) {
            l = new Cons(e, l);
        }
        return l;
    }
    [Symbol.iterator]() {
        return this.toArray()[Symbol.iterator]();
    }
    length() {
        return this.toArray().length;
    }
    cons(e) {
        return new Cons(e, this);
    }
    acons(k, v) {
        return this.cons(new Cons(k, v));
    }
    
}

class Cons extends List {
    constructor(car, cdr) {
	super();
	this.car = car;
	this.cdr = cdr;
    }
    toArray() {
        return [this.car].concat(this.cdr.toArray());
    }
    assq(key) {
        if (this.car instanceof Cons && this.car.car == key) {
            return this.car;
        }
        else {
            return this.cdr.assq(key);
        }
    }

}

class Empty extends List {
    toArray() {
        return [];
    }
    
    assq(key) {
        return false;
    }
}

const nil = new Empty();

function normalize(model, substitution=nil) {
    if (model instanceof LVar) {
	return [model, substitution];
    }
    else if (Array.isArray(model)) {
	let tail = new LVar(substitution.length()); //substitution.push(nil) - 1
        substitution = substitution.acons(tail, nil);
	for (let i=model.length-1; 0<=i; i--) {
            var [lvar, substitution] = normalize(model[i], substitution);
	    tail = new LVar(substitution.length()); //substitution.push(new Cons(lvar, tail)) - 1
            substitution = substitution.acons(lvar, tail);
	}
	return [tail, substitution];
    }
    else if (typeof model == 'object') {
	let m = {};
	for (const k in model) {
	    //log('k',k,'submodel',model[k], 'substitution',JSON.stringify(substitution));
            var [lvar, substitution] = normalize(model[k], substitution);
            const lvar2 = new LVar(substitution.length());
            substitution = substitution.acons(lvar2, lvar);
	    m[k] = lvar2;
            //substitution = substitution.push(new LVar(substitution.push(lvar) - 1)) - 1
	    //log('id',m[k],'substitution',JSON.stringify(substitution));
	}
        const mvar = new LVar(substitution.length());
	return [mvar, substitution.acons(mvar, m)];
    }
    else {
        const lvar = new LVar(substitution.length());
	return [lvar, substitution.acons(lvar, model)];
    }
}

function walk(substitution, lvar) {
    if (!(lvar instanceof LVar)) return lvar;
    const v = substitution.assq(lvar);
    if (v) { return walk(substitution, v.cdr); }
    else return v;
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
        if (spec[0] instanceof LVar) {
            return render([walk(sub, spec[0])].concat(spec.slice(1)), sub, obs, model);
        }
        else if (spec[0] instanceof List) { // Build an iterable DOM list
            let parent = document.createDocumentFragment();
            for (const e of spec[0]) {
                var [node, sub, obs] = render(spec[1], sub, obs, e);
                parent.appendChild(node);
            }
            return [parent, sub, obs];
        } // Build a head node for the rest of the child specs
        else {
	    let parent = document.createElement(spec[0]);
	    for (let i=1; i<spec.length; i++) {
	        log('child render', render(spec[i], sub, obs, model));
                var [node, sub, obs] = render(spec[i], sub, obs, model);
                parent.appendChild(node);
	    }
	    return [parent, sub, obs];
        }
    }
    else if (spec instanceof LVar) { // Build a watched Text node
	var [node, sub, obs] = render(walk(sub, spec), sub, obs, model);
	return [node, sub, obs.cons(new PropObserver(spec, node, 'textContent'))];
    }
    else throw Error('Unrecognized render spec: ' + JSON.stringify(spec));
    //    		typeof child === 'number') head.appendChild(document.createTextNode(child));
    //document.createDocumentFragment());}
}

// UPDATING

function update(sub, obs) {
    for (o of obs) {
        o.update(walk(sub, o.lvar));
    }
}

function update2(lvar, val, sub, obs) {
    let s = [...sub];
    s[lvar.id] = val;
    let observers = obs[lvar.id];
    if (observers) observers.forEach(function (o) { o.update(val) });
    return s;
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
assert(walk(s, m).a instanceof LVar, walk(s, m).a);

//Template
asserte(render(walk(s,m).a, s, nil, m)[0].textContent, '1');

//DOM

var o = nil; // observers: convert substitution values into dom updates

// Static
asserte(render('lorem', s, o, m)[0].textContent, 'lorem'); // Static text node
asserte(render(['div', 'lorem'], s, o, m)[0].innerHTML, 'lorem'); // Static dom node
asserte(render(['div', ['div', 'lorem']], s, o, m)[0].childNodes[0].innerHTML, 'lorem'); // Static nested dom node

// Dynamic
let model = walk(s,m);
var [n,,o] = render(model.a, s, o, m);
asserte(n.textContent, '1');
update(s.acons(model.a, 2), o);
asserte(n.textContent, '2');

// Lists
asserte(render([List.fromArray(['ipsum', 'dolor']), ['div', 'lorem']], s, o, m)[0].childNodes[0].innerHTML, 'lorem');
asserte(render([List.fromArray(['ipsum', 'dolor']), ['div', function (e) { return 'lorem' }]], s, o, m)[0].childNodes[0].innerHTML, 'lorem');
asserte(render([List.fromArray(['ipsum', 'dolor']), ['div', function (e) { return e }]], s, o, m)[0].childNodes[0].innerHTML, 'ipsum');



let [todo_model, todo_substitution] =
    normalize({todos: [{title: 'get todos displaying', done: false},
                       {title: 'streamline api', done: false}]});
let [todo_node] = render(['div',
                          [walk(todo_substitution, todo_model).todos,
                           ['div', 'todo item']]],
                         todo_substitution, nil, todo_model);
document.body.appendChild(todo_node);

console.log('Tests Complete');

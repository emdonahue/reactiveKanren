let logging = false;
function log() {
    if (logging) console.log(arguments);
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
    constructor(node, attr) {
	this.node = node;
	this.attr = attr;
    }

    update(val) {
	this.node[this.attr] = val;
    }
}

class List {

}

class Cons extends List {
    constructor(car, cdr) {
	super();
	this.car = car;
	this.cdr = cdr;
    }
}

class Empty extends List {

}

const nil = new Empty();

function normalize(model, substitution) {
    if (model instanceof LVar) {
	return model;
    }
    else if (Array.isArray(model)) {
	let tail = new LVar(substitution.push(nil) - 1);
	for (let i=model.length-1; 0<=i; i--) {
	    tail = new LVar(substitution.push(new Cons(normalize(model[i], substitution), tail)) - 1);
	}
	return tail;
    }
    else if (typeof model == 'object') {
	let m = {};
	for (const k in model) {
	    m[k] = normalize(model[k], substitution);
	}
	return new LVar(substitution.push(m) - 1);
    }
    else {
	return new LVar(substitution.push(model) - 1);
    }
}

function walk(substitution, lvar) {
    if (!(lvar instanceof LVar)) return lvar;
	return substitution[lvar.id];
}


// RENDERING

function render(spec, sub, obs) {
    log('render', spec, sub, obs);
    assert(sub);
    if (typeof spec == 'string' || typeof spec == 'number') {
	let node = document.createTextNode(spec);
	//return [node, new PropObserver(node, 'textContent')];
	return node;
    }
    else if (Array.isArray(spec)) {
	let parent = document.createElement(spec[0]);
	for (let i=1; i<spec.length; i++) {
	    log('child render', render(spec[i], sub, obs));	    
	    parent.appendChild(render(spec[i], sub, obs));
	}
	return parent;
    }
    else if (spec instanceof LVar) {
	let node = render(walk(sub, spec), sub, obs);
	obs[spec.id] = (obs[spec.id] || []);
	obs[spec.id].push(new PropObserver(node, 'textContent'));
	return node;
    }
    else throw Error('Unrecognized render spec: ' + JSON.stringify(spec));
    //    		typeof child === 'number') head.appendChild(document.createTextNode(child));
    //document.createDocumentFragment());}
}

// UPDATING

function update(lv, val, obs) {
    
}


// TESTING

let s = [];
let m = normalize({
    a: 1,
    b: 2,
    c: [3, 4],
    d: {e: 5, f: 6}
}, s);




log("model",m);
log("substitution",s);

assert(walk(s, m).a instanceof LVar, walk(s, m).a);
asserte(render(walk(s,m).a, s, []).textContent, '1');

let o = [];
let n = render(walk(s,m).a, s, o);
asserte(n.textContent, '1');
walk(o,walk(s,m).a)[0].update(2);
asserte(n.textContent, '2');


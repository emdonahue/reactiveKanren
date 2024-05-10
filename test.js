//TODO make set unify always pick the non temporary variable to set. maybe insert special perma vars with normalize
//TODO can we quote vars to preserve references?
//TODO can setunify(quote(var), val) let us arbitrarily unquote quotes?

import {nil, cons, list, Pair, List, LVar, primitive, fresh, conde, unify, setunify, reunify, normalize2, succeed, fail, failure, Goal, QuotedVar} from './mk.js'
import {logging, log, dlog, copy, toString} from './util.js'

function test(f, test_name) {
    try {
	f();
    } catch (x) {
	document.write('error in test: ' + (test_name || 'Unnamed'));
	throw x;
    }
}

function equals(a, b) {
    return JSON.stringify(a) == JSON.stringify(b);
}

function asserte(a, b) {
    if (!equals(a, b)) throw Error(toString(a) + ' != ' + toString(b));
}









//(spec, sub=nil, obs=nil, model={}, update=()=>{})
class App {
    constructor(model, template) {
        let [m, s] = normalize2(model);
        this.model = new LVar();
        s = s.acons(this.model, m);
        let [n, s2, o, g] = render(template, s, nil, this.model, this.update.bind(this));
        console.assert(g);
        log('init', 'goals', g);
        this.substitution = s2;
        this.observers = o;
        this.node = n;
        this.goals = g;
        this.update(succeed);
    }
    update(g) {
        log('update', 'goal', 'setunify', g);
        log('update', 'goal', 'derived', this.goals);
        log('update', 'model', this.model);
        log('update', 'sub', 'prev', this.substitution);
        let ans = this.goals.conj(g).run(1, {reify:false, substitution: this.substitution});
        if (ans === nil) throw new Error('Update goal failed: ' + g);
        let s = ans.car.substitution;
        s = garbage_collect(s, this.model);
        log('update', 'sub', 'updated', s);
        s = this.goals.run(1, {reify:false, substitution: s}).car.substitution;
        log('update', 'sub', 'derived', s);
        if (2 === failure) throw Error('Update goal failed' + to_string(g));
        let o;
        [s, o] = this.observers.fold(([sub, obs], o) => o.update(sub, obs), [s, nil]);
        log('update', 'observers', o);
        this.substitution = garbage_collect(s, this.model);
        this.observers = o;
    }
}

// RRP
class PropObserver {
    constructor(lvar, node, attr) {
        this.lvar = lvar;
	this.node = node;
	this.attr = attr;
    }

    update(sub, obs) {
        let val = sub.walk(this.lvar);
        log('update', 'attr', this.attr, this.lvar, val);
        if (val instanceof LVar) return [sub, obs];
	this.node[this.attr] = val;
        return [sub, obs.cons(this)];
    }
    toString() { return `(${this.lvar} ${this.attr})` }
}

class StyleObserver extends PropObserver{
    update(sub, obs) {
        let val = sub.walk(this.lvar);
        log('update', 'style', this.attr, this.lvar, val);
        if (val instanceof LVar) return [sub, obs];
	this.node.style[this.attr] = val;
        return [sub, obs.cons(this)];
    }
}

/*
  [X 1 2 3] insert before
  [1 2 3 X] append child
  [1 X 2 3] insert before
  [X 2 3] no change. if no change, always just update. dont reshuffle. therefore we just need to either eliminate the least wasteful or insert the most strategic. we detect this when a pair is replaced with null, or null with items



*/

class IterObserver {
    constructor(lvar, node, lvar_nodes, template) {
        //dlog('iter observer', lvar_nodes)
        this.lvar = lvar;
        this.node = node;
        this.lvar_nodes = lvar_nodes;
        this.template = template;
    }
    toString() { return `(${this.lvar} ${toString(this.template)})` }
    update(sub, obs) {
        // get list of vars still in store
        // remove nodes for all variables no longer in store
        // for all vars in store,
//        return [sub, obs.cons(this)];
        let ns = this.moddom(this.lvar, sub);
        dlog('ns', ns, this.lvar_nodes)
        dlog('sub', sub)
        this.lvar_nodes = this.lvar_nodes.filter(b => {
            if (ns.member(b.car)) return true;
            dlog('removing', b.car)
            b.cdr.remove();
            return false;
        }).append(ns.filter(v => !this.lvar_nodes.assoc(v)).map(v => {
            let node;
            [node, sub, obs] = render(this.template, sub, nil, sub.walk(v).car, () => {});
            this.node.parentNode.insertBefore(node, this.node);
            return cons(v, node);
        }));
        dlog('lvar nodes', this.lvar_nodes);
                    /*
        this.lvar_nodes = this.lvar_nodes.filter(
            function ({car:v, cdr:n}) {
                dlog('walk', v, sub.walk(v))
                if (!(sub.walk(v) instanceof Pair)) {
                    console.log('remove', sub.walk(v))
                    n.remove();
                    return false; }
                return true;
            });
*/
        //if (val instanceof Pair) return true;
        //this.node.remove();
        //return false;
        return [sub, obs.cons(this)];
    }
    moddom(lvar, sub) {
        let w = sub.walk(lvar);
        if (w === nil) {
            return nil;
        }
        console.assert(w instanceof Pair, w);
        return this.moddom(w.cdr, sub).cons(lvar);
    }

}



// MK


// RRP



// RENDERING

function render(spec, sub=nil, obs=nil, model={}, update=()=>{}, goals=succeed) { // -> node substitution observers
    log('render', spec, sub, obs, model, goals);
    console.assert(obs instanceof List, obs);
    if (typeof spec == 'string' || typeof spec == 'number') { // Simple Text nodes
	let node = document.createTextNode(spec);
	return [node, sub, obs, goals]; }
    else if (spec instanceof LVar) { // Build a watched Text node
        if (sub.walk(spec) instanceof LVar) throw new Error('Rendering free var: ' + spec); //DBG
	var [node, sub, obs, goals] = render(sub.walk(spec), sub, obs, model, update, goals);
	return [node, sub, obs.cons(new PropObserver(spec, node, 'textContent')), goals]; }
    else if (spec instanceof Function) { // Build a dynamic node using the model
        let v = new LVar();
        let g = spec(v, model);
        if (g instanceof Goal) {
            let s = g.run(1, {reify: false, substitution: sub}).car.substitution;
            if (failure === s) throw new Error('Derived goal failure: ' + sub.reify(g));
            log('render', 'fn', s.reify(g), s.reify(v));
            return render(v, s, obs, model, update, goals.conj(g)); }
        else { return render(g, sub, obs, model, update, goals); }}
    else if (Array.isArray(spec)) return render_head(spec, sub, obs, model, update, goals);
    else throw Error('Unrecognized render spec: ' + JSON.stringify(spec));
}

function render_head([templ_head, ...templ_children], sub, obs, model, update, goals) { //Render DOM tree
    let head_spec = sub.walk(templ_head);
    if (Array.isArray(head_spec)) return render_head([list(...head_spec), ...templ_children], sub, obs, model, update, goals); // Convert arrays to lists
    else if (typeof head_spec == 'string'){ // Strings are tagNames
        return render([{tagName:head_spec}, ...templ_children], sub, obs, model, update, goals); } //TODO redirect recursions to head reander
    else if (head_spec instanceof Function) { // Dynamic head node
        let v = new LVar();
        let g = head_spec(v, model);
        let s = g.run(1, {reify: false, substitution: sub}).car.substitution;
        log('render', 'head', 'fn', s.reify(g));
        return render([v, ...templ_children], s, obs, model, update, goals.conj(g)); }
    else if (head_spec instanceof List) { // Build an iterable DOM list
        let parent = document.createDocumentFragment();
        let items = head_spec;
        let linkvar = templ_head;
        let listvar = templ_head; //TODO in simple static list cases this may not be a var
        if (listvar instanceof LVar) listvar.name('list');
        let listnode = document.createComment('');
        let vars_nodes = [];

        while (items instanceof Pair) { //TODO deal with lvar tailed improper lists
            var [node, sub, obs, goals] = render(templ_children[0], sub, obs, items.car, update, goals);
            parent.appendChild(node);
            vars_nodes.push(cons(linkvar, node));
            linkvar = items.cdr;
            items = sub.walk(linkvar);
        }
        return [parent.appendChild(listnode) && parent, sub, obs.cons(new IterObserver(listvar, listnode, list(...vars_nodes), templ_children[0])), goals];
    }
    else if (head_spec.prototype === undefined) { // POJOs store node properties
        let parent = document.createElement(head_spec.tagName || 'div');
        [obs, goals] = render_attributes(head_spec, parent, sub, model, obs, goals, update);
        
	for (let c of templ_children) { // Render child nodes
            var [node, sub, obs, goals] = render(c, sub, obs, model, update, goals);
            parent.appendChild(node);
	}
	return [parent, sub, obs, goals]; }
    else throw Error('Unrecognized render spec head: ' + JSON.stringify(head_spec));
}

function render_attributes(template, parent, sub, model, obs, goals, update) {
    for (let k in template) {
        if (k === 'tagName') continue; // tagName already extracted explicitly in construction of parent.
        else if (k === 'style') [obs, goals] = render_attributes(template[k], parent.style, sub, model, obs, goals, update);
        else if (primitive(template[k])) parent[k] = template[k];
        else if (k.substring(0,2) == 'on') { // event listeners
            log('render', 'on', k.substring(2));
            (handler => {
                parent.addEventListener(
                    k.substring(2),
                    function(e) {
                        if (handler instanceof Goal) update(handler);
                        else if (handler instanceof Function) update(handler(model, e));
                        else throw new Error('Unrecognized event handler type: ' + handler);
                    }
                );})(template[k]); }
        else if (template[k] instanceof Function) {
            let v = new LVar();
            let g = template[k](v, model);
            let s = g.filter(g => !g.is_disj()).run(1, {reify: false, substitution: sub}).car.substitution;
            parent[k] = s.walk(v);
            obs = obs.cons(new PropObserver(v, parent, k));
            log('render', 'goals', g, '=>', g.filter(g => g.is_disj()));
            goals = goals.conj(g); }} //.filter(g => g.is_disj())
    return [obs, goals];
}

// UPDATING



function garbage_collect(sub, root) {
    return garbage_sweep(sub, garbage_mark(sub, root));
}

function garbage_mark(sub, root, marked=nil) {
    // Return vars in sub still reachable from root.
    log('garbage_mark', root, marked);
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




let [m, s] = normalize2({
    a: 1,
    b: 2,
    c: [3, 4],
    d: {e: 5, f: 6}
}, nil);

log("model",m);
log("substitution",s);

//Model
console.assert(s.walk(m).a instanceof LVar, s.walk(m).a);
asserte(garbage_mark(s, m).length(), 10);
asserte(garbage_mark(s.acons(m.c, m.a), m).length(), 6);
asserte(garbage_sweep(s, garbage_mark(s.acons(m.c, m.a), m)).length(), 6);

//Template
asserte(render(s.walk(m).a, s, nil, m)[0].textContent, '1');

//DOM

var o = nil; // observers: convert substitution values into dom updates

// Static
asserte(render('lorem', s, o, m)[0].textContent, 'lorem');
asserte(render(['div', 'lorem'], s, o, m)[0].innerHTML, 'lorem');
asserte(render([{tagName: 'div'}], s, o, m)[0].tagName, 'DIV');
asserte(render([{tagName: 'div', name: 'lorem'}], s, o, m)[0].name, 'lorem');
asserte(render(['div', ['div', 'lorem']], s, o, m)[0].childNodes[0].innerHTML, 'lorem');

// Dynamic
var [n,,o] = render(s.walk(m).a, s, o, m);
asserte(n.textContent, '1');
//update(s.acons(s.walk(m).a, 2), o);
//asserte(n.textContent, '2');

// Lists
asserte(render([list('ipsum', 'dolor'), ['div', 'lorem']], s, o, m)[0].childNodes[0].innerHTML, 'lorem');
asserte(render([list('ipsum', 'dolor'), ['div', function (v) { return unify(v, 'lorem') }]], s, o, m)[0].childNodes[0].innerHTML, 'lorem');
asserte(render([list('ipsum', 'dolor'), ['div', function (v, m) { return unify(v, m) }]], s, o, m)[0].childNodes[0].innerHTML, 'ipsum');

// TDList
let data = {todos: [{title: 'get tds displaying', done: false},
                    {title: 'streamline api', done: true}],
            selected: new QuotedVar({title: 'Untitled', done: false})};
let template = (_,m) => ['div',
                         [(todos, m) => unify({todos: todos}, m),
                          [{style: {color: (color, todo) => conde([unify({done: true}, todo), unify(color, 'green')],
                                                                  [unify({done: false}, todo), unify(color, 'black')])}},
                           [{tagName: 'input', type: 'checkbox', checked: (done, todo) => unify({done: done}, todo),
                             onchange: m => conde([unify({done: true}, m), setunify(m, {done: false})], //TODO make goals directly returnable?
                                                  [unify({done: false}, m), setunify(m, {done: true})])}],
                           [{tagName: 'span',
                             onclick: todo => setunify(m, {selected: todo.quote()})},
                            (title, todo) => unify({title: title.name('selected.title/set')}, todo)]]],
                         [{onclick: setunify(m, {selected: new QuotedVar({title: 'SETTITLE'})})}, (selected, todo) => fresh(sel => [unify(todo, {selected: sel.quote()}),
                                                                   unify(sel, {title: selected.name('selected.title/get')})])]];

/*
[td_sub.walk(m).todos,
                        [{onclick: m => {console.log('click model', m); return fresh(x => [unify({title: x}, m), setunify(x, 'event handler works')])}},
                         function (e) {return td_sub.walk_path(e, 'title')}]]
*/

//logging()





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

asserte(succeed.run(), list(nil));
asserte(fresh((x) => unify(x, 1)).run(), List.fromTree([[1]]));
asserte(fresh((x, y) => [x.unify(1), y.unify(2)]).run(), List.fromTree([[1, 2]]));
asserte(fresh((x) => [x.unify(1), x.unify(2)]).run(), nil);
asserte(fresh((x, y) => unify(cons(x,y), cons(1,2))).run(), List.fromTree([[1, 2]]));
asserte(fresh((x, y) => unify({a:x, b:y}, {a:1, b:2})).run(), List.fromTree([[1, 2]]));
asserte(fresh((x) => unify({a:1, b:x}, {a:1, b:2})).run(), List.fromTree([[2]]));
asserte(fresh((x) => unify({b:x}, {a:1, b:2})).run(), List.fromTree([[2]]));
asserte(fresh((x) => unify({a:1, b:2}, {b:x})).run(), List.fromTree([[2]]));
asserte(fresh((x) => conde(x.unify(1), x.unify(2))).run(2), List.fromTree([[1], [2]]));
asserte(fresh((x,y) => [unify(x,cons(1, y)), unify(y,cons(2, nil))]).run(), List.fromTree([[list(1, 2), list(2)]]));
asserte(fresh(x => [conde(unify(x,1), unify(x,1)), unify(x,1)]).run(), List.fromTree([[1], [1]]));

asserte(fresh((x) => [unify(x, 1), reunify(x, 2)]).run(), List.fromTree([[2]]));

asserte(fresh((x) => setunify(x, 1)).run(), List.fromTree([[1]]));
asserte(fresh((x) => [unify(x,2), setunify(x, 1)]).run(), List.fromTree([[1]]));
asserte(fresh((x) => [unify(x,cons(1,2)), setunify(x, 1)]).run(), List.fromTree([[1]]));
asserte(fresh((x,y,z) => [unify(x,cons(y,z)), setunify(x, cons(1,2))]).run(), List.fromTree([[cons(1, 2), 1, 2]]));
asserte(fresh((x) => [unify(x,1), setunify(x, cons(1,2))]).run(), List.fromTree([[cons(1, 2)]]));
asserte(fresh((x,y,z) => [unify(x,{a:y,b:z}), unify(y,1), unify(z,2), setunify(x, {a:1,b:3})]).run(), List.fromTree([[{a:1,b:3}, 1, 3]]));
asserte(fresh((x,y) => [unify(x,{a:y}), unify(y,1), setunify(x, {a:1,b:3})]).run(), List.fromTree([[{a:1,b:3}, 1]]));
asserte(fresh((x,y,z) => [unify(x,{a:y,b:z}), unify(y,1), unify(z,2), setunify(x, {b:3})]).run(), List.fromTree([[{a:1, b:3}, 1, 3]]));
asserte(fresh((x,y) => [unify(x.name('x'),1), unify(y.name('y'),2), setunify(x, y), setunify(y,x)]).run(), List.fromTree([[2, 1]]));

asserte(fresh((w,x,y,z) => [unify(x,cons(1, y)), unify(y,cons(2, nil)), unify(x,w),unify(x,cons(1, z)), setunify(w, z)]).run(), List.fromTree([[[1], [1], [], []]])); // x,w:(1 . y,z:(2)) -> x,w:(2 . y,z:())

asserte(fresh((a,b,c,d,x,y) => [unify(a, {prop: b}), unify(b,1),
                                unify(c, {prop: d}), unify(d,2),
                                unify(x,cons(a, y)), unify(y,cons(c, nil)),
                                setunify(x, y)]).run(),
        List.fromTree([[{prop:2}, 2, {prop:2}, 2, [{prop:2}], []]]));


logging('update');
//logging('unify');
//logging('init');
logging('render');
let app = new App(data, template);
document.body.appendChild(app.node);
console.log('Tests Complete');

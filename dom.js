import {nil, cons, list, Pair, List, LVar, primitive, fresh, conde, unify, setunify, reunify, normalize, succeed, fail, failure, Goal, quote} from './mk.js'
import {logging, log, dlog, copy, toString} from './util.js'

class App {
    constructor(model, template) {
        let [m, s] = normalize(model);
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
        //dlog('ns', ns, this.lvar_nodes)
        //dlog('sub', sub)
        this.lvar_nodes = this.lvar_nodes.filter(b => {
            if (ns.member(b.car)) return true;
            //dlog('removing', b.car)
            b.cdr.remove();
            return false;
        }).append(ns.filter(v => !this.lvar_nodes.assoc(v)).map(v => {
            let node;
            [node, sub, obs] = render(this.template, sub, nil, sub.walk(v).car, () => {});
            this.node.parentNode.insertBefore(node, this.node);
            return cons(v, node);
        }));
        //dlog('lvar nodes', this.lvar_nodes);
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
    log('render', spec, Array.isArray(spec) ? 'array' : typeof spec, sub, obs, model, goals);

    if (typeof spec == 'string' || typeof spec == 'number') { // Simple Text nodes
	let node = document.createTextNode(spec);
        log('render', 'text', spec, node);
	return [node, sub, obs, goals]; }
    else if (spec instanceof LVar) { // Build a watched Text node
        log('render', 'var', spec);
        if (sub.walk(spec) instanceof LVar) throw new Error('Rendering free var: ' + spec); //DBG
	var [node, sub, obs, goals] = render(sub.walk(spec), sub, obs, model, update, goals);
        log('render', 'var', spec, node.outerHTML);
	return [node, sub, node.nodeType == Node.TEXT_NODE ? obs.cons(new PropObserver(spec, node, 'textContent')) : obs, goals]; }
    else if (spec instanceof Function) { // Build a dynamic node using the model
        return render_fn(spec, sub, model, goals, (r, s, g) => render(r, s, obs, model, update, g)); }
    else if (Array.isArray(spec)) return render_head(spec, sub, obs, model, update, goals);
    else throw Error('Unrecognized render spec: ' + JSON.stringify(spec)); }

function render_head([templ_head, ...templ_children], sub, obs, model, update, goals) { //Render DOM tree
    let head_spec = sub.walk(templ_head);
    log('render', 'head', head_spec);
    if (Array.isArray(head_spec)) return render_head([list(...head_spec), ...templ_children], sub, obs, model, update, goals); // Convert arrays to lists
    else if (typeof head_spec == 'string'){ // Strings are tagNames
        return render_head([{tagName:head_spec}, ...templ_children], sub, obs, model, update, goals); } //TODO redirect recursions to head reander
    else if (head_spec instanceof Function) { // Dynamic head node
        return render_fn(head_spec, sub, model, goals, (r, s, g) => render_head([r, ...templ_children], s, obs, model, update, g)); }
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
            items = sub.walk(linkvar); }
        return [parent.appendChild(listnode) && parent, sub, obs.cons(new IterObserver(listvar, listnode, list(...vars_nodes), templ_children[0])), goals]; }
    else if (head_spec.prototype === undefined) { // POJOs store node properties
        if (head_spec.tagName && typeof head_spec.tagName != 'string') throw new Error('tagName must be a string: ' + head_spec.tagName); //TODO make tagName accept fns and goals
        let parent = document.createElement(head_spec.tagName || 'div');
        [obs, goals] = render_attributes(head_spec, parent, sub, model, obs, goals, update);
        
	for (let c of templ_children) { // Render child nodes
            var [node, sub, obs, goals] = render(c, sub, obs, model, update, goals);
            log('render', 'child', c, node.outerHTML);
            parent.appendChild(node);
            log('render', 'parent', parent.outerHTML); }
	return [parent, sub, obs, goals]; }
    else throw Error('Unrecognized render spec head: ' + JSON.stringify(head_spec)); }

function render_attributes(template, parent, sub, model, obs, goals, update) {
    log('render', 'attributes', template);
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
            let v;
            [v, sub, goals] = render_fn(template[k], sub, model, goals, (r, s, g) => [r, s, g]);
            parent[k] = sub.walk(v);
            /*
            let v = new LVar();
            let g = template[k](v, model);
            let s = g.filter(g => !g.is_disj()).run(1, {reify: false, substitution: sub}).car.substitution;
            parent[k] = s.walk(v);
            obs = obs.cons(new PropObserver(v, parent, k));
            log('render', 'goals', g, '=>', g.filter(g => g.is_disj()));
            goals = goals.conj(g);*/ }} //.filter(g => g.is_disj())
    return [obs, goals];
}

function render_fn(templ, sub, model, goals, rndr) {
    log('render', 'fn', templ);
    let v = new LVar();
    let g = templ(v, model);
    if (g instanceof Goal) {
        let ss = g.run(1, {reify: false, substitution: sub});
        if (nil === ss) throw new Error('Derived goal failure: ' + sub.reify(g));
        log('render', 'fn', templ, ss.car.substitution.walk(v));
        return rndr(v, ss.car.substitution, goals.conj(g)); }
    else { return rndr(g, sub, goals); }}


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

export {App, render, garbage_mark, garbage_sweep};

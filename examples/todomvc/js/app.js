import {RK, nil, LVar, SVar, list, unify, quote, succeed, fresh, List, cons, conde, reunify, conj, fail, view} from '../../../mk.js'

import {logging} from '../../../util.js';

(function (window) {
	'use strict';

    let data = {todos: list({title: 'Taste JavaScript', done: true}, {title: 'Buy a unicorn', done: false}),
                active: true,
                completed: true}
    
    

    function template(m) {
        return [{tagName: 'section', className: 'todoapp'},
                [{tagName: 'header', className: 'header'},
                 ['h1', 'todos'],
                 [{tagName: 'input', className: 'new-todo', placeholder: 'What needs to be done?', autofocus: true,
                   onkeydown: e => {
                       if (e.key === 'Enter') {
                           let title = e.target.value;
                           e.target.value = '';
                           return fresh((todos, x) => [m.eq({todos: todos}), todos.tailo(x), x.set(list({title: title, done: false}))]);}}}]],
                [{tagName: 'section', className: 'main'},
                 [{tagName: 'input', id: 'toggle-all', className: 'toggle-all', type: 'checkbox'}],
                 [{tagName: 'label', for: 'toggle-all'}, 'Mark all as complete'], items_template(m)],
                [{tagName: 'footer', className: 'footer'},
                 [{tagName: 'span', className: 'todo-count'}, ['strong', 0], ' item left'],
                 [{tagName: 'ul', className: 'filters'},
                  ['li', [{tagName: 'a', className: 'selected', href: '#/',
                           onclick: m.set({active: true, completed: true})}, 'All']],
                  ['li', [{tagName: 'a', href: '#/active',
                           onclick: m.set({active: true, completed: false})}, 'Active']],
                  ['li', [{tagName: 'a', href: '#/completed',
                           onclick: m.set({active: false, completed: true})}, 'Completed']]],
                 [{tagName: 'button', className: 'clear-completed'}, 'Clear completed']]]; }

    function items_template(m) {
        return [{tagName: 'ul', className: 'todo-list'},
                v =>
                fresh((todos, title, done, strikethru, active, completed) =>
                    [m.eq({todos: todos, active: active, completed: completed}),
                     todos.membero({title: title, done: done}),
                     conde([done.eq(true), completed.eq(true), strikethru.eq('completed')],
                           [done.eq(false), active.eq(true), strikethru.eq('')]),
                     v.eq([{tagName: 'li', className: strikethru,
                            onclick: done.negate()},
                           [{tagName: 'div', className: 'view'},
                            [{tagName: 'input', className: 'toggle', type: 'checkbox', checked: done}],
                            ['label', title],
                            [{tagName: 'button', className: 'destroy'}]],
                           [{tagName: 'input', className: 'edit', value: 'Create a TodoMVC template'}]])])] }

    //logging('render') //|| logging('parse') || logging('rerender') || logging('expand')
    let app = new RK(template, data);
    
    document.getElementById('root').replaceWith(app.root());
    logging('reunify')

/*
[{tagName: 'li', className: 'completed'},
                 [{tagName: 'div', className: 'view'},
                  [{tagName: 'input', className: 'toggle', type: 'checkbox', checked: true}],
                  ['label', 'Taste JavaScript'],
                  [{tagName: 'button', className: 'destroy'}]],
                 [{tagName: 'input', className: 'edit', value: 'Create a TodoMVC template'}]],
                [{tagName: 'li'},
                 [{tagName: 'div', className: 'view'},
                  [{tagName: 'input', className: 'toggle', type: 'checkbox'}],
                  ['label', 'Buy a unicorn'],
                  [{tagName: 'button', className: 'destroy'}]],
                 [{tagName: 'input', className: 'edit', value: 'Rule the web'}]]
*/
    
})(window);

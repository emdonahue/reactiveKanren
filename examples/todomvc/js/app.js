import {RK, nil, LVar, SVar, list, unify, quote, succeed, fresh, List, cons, conde, reunify, conj, fail, render as render, view} from '../../../mk.js'

(function (window) {
	'use strict';

    let template =
        [{tagName: 'section', className: 'todoapp'},
         [{tagName: 'header', className: 'header'},
          ['h1', 'todos'],
          [{tagName: 'input', className: 'new-todo', placeholder: 'What needs to be done?', autofocus: true}]],
         [{tagName: 'section', className: 'main'},
          [{tagName: 'input', id: 'toggle-all', className: 'toggle-all', type: 'checkbox'}],
          [{tagName: 'label', for: 'toggle-all'}, 'Mark all as complete'],
          [{tagName: 'ul', className: 'todo-list'},
           [{tagName: 'li', className: 'completed'},
            [{tagName: 'div', className: 'view'},
             [{tagName: 'input', className: 'toggle', type: 'checkbox', checked: true}],
             ['label', 'Taste JavaScript'],
             [{tagName: 'button', className: 'destroy'}]],
            [{tagName: 'input', className: 'edit', value: 'Create a TodoMVC template'}]],
           [{tagName: 'li'},
            [{tagName: 'div', className: 'view'},
             [{tagName: 'input', className: 'toggle', type: 'checkbox', checked: true}],
             ['label', 'Buy a unicorn'],
             [{tagName: 'button', className: 'destroy'}]],
            [{tagName: 'input', className: 'edit', value: 'Rule the web'}]]]],
         [{tagName: 'footer', className: 'footer'},
          [{tagName: 'span', className: 'todo-count'}, ['strong', 0], ' item left'],
          [{tagName: 'ul', className: 'filters'},
           ['li', [{tagName: 'a', className: 'selected', href: '#/'}, 'All']],
           ['li', [{tagName: 'a', href: '#/active'}, 'Active']],
           ['li', [{tagName: 'a', href: '#/completed'}, 'Completed']]],
          [{tagName: 'button', className: 'clear-completed'}, 'Clear completed']]];
    
    let app = new RK(template);
    document.getElementById('root').replaceWith(app.render());

})(window);

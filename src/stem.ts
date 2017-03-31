/**
 * The MIT License (MIT)
 * Copyright (c) Taketoshi Aono
 *  
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *  
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *  
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * @fileoverview 
 * @author Taketoshi Aono
 */


import {
  FuelElement,
  FuelDOMNode,
  SharedEventHandler,
  Stem,
  FuelComponent,
  FuelComponentStatic,
  CONVERSATION_TABLE,
  DOMEvents
} from './type';
import {
  setStyle
} from './node';
import {
  fastCreateDomTree,
  cleanupTree
} from './tree';
import {
  FuelElementView
} from './element';
import {
  Difference,
  AttrState,
  DifferenceBits,
  isCreateChildren,
  isNewElement,
  isRemoveElement,
  isReplaceElement,
  isTextChanged,
  diff
} from './difference';
import {
  Renderer
} from './renderer/renderer';
import {
  invariant,
  requestAnimationFrame,
  requestIdleCallback,
  merge
} from './util';


type PatchStackType = {
  context: any,
  newElement: FuelElement,
  oldElement: FuelElement,
  newChildren: FuelElement[],
  oldChildren: FuelElement[],
  parsed: boolean,
  difference: Difference,
  root: FuelElement;
  isKeyedItem: boolean;
};


function createStem() {
  return new FuelStem();
}


function replaceElement(root: FuelElement, parent: FuelElement, oldElement: FuelElement, newElement: FuelElement, isKeyedItems: boolean, renderer: Renderer) {
  const newDom = FuelElementView.createDomElement(root, newElement, renderer, createStem);
  const oldDom = oldElement.dom;
  if (oldDom.nodeType === 1 && newDom.nodeType === 1) {
    const children = oldDom.children;
    while (children.length) {
      newDom.appendChild(children[0]);
    }
  }

  const parentDom = parent.dom;
  if (!isKeyedItems) {
    parentDom.replaceChild(newDom, oldDom);
  } else {
    parentDom.removeChild(oldDom);
    parentDom.appendChild(newDom);
  }
}


function copyElementRef(root: FuelElement, oldElement: FuelElement, newElement: FuelElement, isKeyedItem: boolean) {
  newElement.dom = oldElement.dom;
  FuelElementView.attachFuelElementToNode(newElement.dom, newElement);
  if (isKeyedItem) {
    newElement.dom.parentNode.appendChild(newElement.dom);
  }
}


function updateElement(diff: Difference, rootElement: FuelElement, newElement: FuelElement) {
  const domElement = newElement.dom;
  const strippedRoot = FuelElementView.stripComponent(rootElement);
  for (let i = 0, len = diff.attr.length; i < len; i++) {
    const {key, value, state} = diff.attr[i];
    switch (state) {
    case AttrState.NEW:
    case AttrState.REPLACED:
      if (DOMEvents[key]) {
        const lowerKey = key.slice(2).toLowerCase();
        strippedRoot._stem.getEventHandler().replaceEvent(newElement.dom, lowerKey, value as any);
      } else {
        domElement[key] = value;
      }
      break;
    case AttrState.STYLE_CHANGED:
      for (const style in value as any) {
        const val = value[style];
        setStyle(domElement, style, val);
      }
      break;
    case AttrState.REMOVED:
      if (DOMEvents[key]) {
        const lowerKey = key.slice(2).toLowerCase();
        strippedRoot._stem.getEventHandler().removeEvent(newElement.dom, lowerKey);
      } else {
        domElement.removeAttribute(key);
      }
    default:
    }
  }
}


interface Batch {
  root: FuelElement,
  parent: FuelElement,
  newElement: FuelElement,
  oldElement: FuelElement,
  isKeyedItem: boolean,
  difference: Difference,
  context: any;
}


function update(batches: Batch[]) {
  const {renderer} = FuelStem;
  for (let i = 0, len = batches.length; i < len; i++) {
    let {parent, newElement, oldElement, isKeyedItem, difference, root, context} = batches[i];
    if (isNewElement(difference)) {
      if (parent) {
        parent.dom.appendChild(fastCreateDomTree(context, root, newElement, renderer, createStem))
        FuelElementView.invokeDidMount(newElement);
      } else {
        const tree = fastCreateDomTree(context, root, newElement, renderer, createStem);
        if (oldElement) {
          parent.dom.appendChild(tree);
          FuelElementView.invokeDidMount(newElement);
          FuelElementView.invokeWillUnmount(oldElement);
        }
      }
    } else if (isRemoveElement(difference)) {
      FuelElementView.invokeWillUnmount(oldElement);
      oldElement.dom.parentNode.removeChild(oldElement.dom);
      oldElement._stem = null;
    } else if (isReplaceElement(difference)) {
      FuelElementView.invokeWillUnmount(oldElement);
      replaceElement(root, parent, oldElement, newElement, isKeyedItem, renderer);
      FuelElementView.invokeDidMount(newElement);
    } else if (isTextChanged(difference)) {
      newElement.dom = oldElement.dom;
      FuelElementView.attachFuelElementToNode(newElement.dom, newElement);
      newElement.dom.textContent = FuelElementView.getTextValueOf(newElement);
      FuelElementView.invokeDidUpdate(newElement);
    } else {
      copyElementRef(root, oldElement, newElement, isKeyedItem);
      updateElement(difference, root, newElement);
      FuelElementView.invokeDidUpdate(newElement);
    }

    if (isCreateChildren(difference)) {
      fastCreateDomTree(context, root, newElement, renderer, createStem);
    }
  }
}


function makeInitialStackState(context, newElement: FuelElement, oldElement: FuelElement): PatchStackType[] {
  return [
    {
      newElement,
      oldElement,
      newChildren: null,
      oldChildren: null,
      parsed: false,
      difference: null,
      context,
      root: newElement,
      isKeyedItem: false
    }
  ];  
}


function createNextStackState(context: any, parentState: PatchStackType, prev: PatchStackType, oldElement: FuelElement): PatchStackType {
  let newChild = prev.newChildren.shift();
  let oldChild: FuelElement;
  let isKeyedItem = false;

  if (parentState) {
    const {newElement: parentNewElement, oldElement: parentOldElement} = parentState;

    if (parentOldElement && parentOldElement._keymap && newChild && parentOldElement._keymap[newChild.key]) {
      oldChild = parentOldElement._keymap[newChild.key];
      if (parentNewElement && !parentNewElement._keymap) {
        parentNewElement._keymap = {};
        parentNewElement._keymap[newChild.key] = newChild;
      }
      const index = prev.oldChildren.indexOf(oldChild);
      if (index !== -1) {
        prev.oldChildren.splice(index, 1);
        isKeyedItem = true; 
      } else {
        oldChild = prev.oldChildren.shift();
        isKeyedItem = false;
      }
    } else {
      oldChild = prev.oldChildren.shift();
      isKeyedItem = false;
    }
  } else {
    oldChild = prev.oldChildren.shift();
    isKeyedItem = false;
  }

  let root = prev.root;
  if (newChild) {
    if (newChild._unmounted) {
      newChild = null;
    } else if (newChild._stem) {
      root = newChild;
    }
  }

  if (newChild && !newChild._ownerElement) {
    newChild._ownerElement = prev.newElement._ownerElement;
  }

  return {
    newElement: newChild,
    oldElement: oldChild,
    newChildren: null,
    oldChildren: null,
    parsed: false,
    difference: null,
    root,
    context,
    isKeyedItem
  };
}


function patchComponent(context: any, newElement: FuelElement, oldElement: FuelElement) {
  if (newElement && FuelElementView.isComponent(newElement)) {
    if (oldElement && oldElement.type !== newElement.type) {
      while (newElement && FuelElementView.isComponent(newElement)) {
        [newElement, context] = FuelElementView.instantiateComponent(context, newElement);
      }
    } else {
      while (newElement && FuelElementView.isComponent(newElement)) {
        if (newElement && oldElement && newElement.type === oldElement.type) {
          newElement._componentInstance = oldElement._componentInstance;
        }
        let revealedOldElement = oldElement;
        if (oldElement && FuelElementView.isComponent(oldElement)) {
          revealedOldElement = FuelElementView.getComponentRenderedTree(oldElement);
        }
        const [stripedNewTree, newContext] = FuelElementView.instantiateComponent(context, newElement, oldElement);
        context = newContext;
        oldElement = revealedOldElement;
        newElement = stripedNewTree;
      }
    }
  }

  if (oldElement && FuelElementView.isComponent(oldElement)) {
    oldElement = FuelElementView.stripComponent(oldElement);
  }

  return [context, newElement, oldElement];
}


export class FuelStem implements Stem {
  public static renderer: Renderer;

  private _enabled = true;

  private batchs: Batch[] = [];

  private batchCallback: () => void = null;

  private sharedEventHandler: SharedEventHandler;

  private lock: boolean = false;

  private renderQueue: {element: FuelElement, cb: (el: FuelDOMNode) => void}[] = [];

  constructor(private tree: FuelElement = null) {}

  public enterUnsafeUpdateZone(cb: () => void) {
    this._enabled = false;
    cb();
    this._enabled = true;
  }


  public registerOwner(owner: FuelElement) {
    this.tree = owner;
  }


  public owner(): FuelElement {
    return this.tree;
  }


  public setEventHandler(handler: SharedEventHandler) {
    this.sharedEventHandler = handler;
  }


  public getEventHandler() {
    return this.sharedEventHandler;
  }


  private renderAtAnimationFrame() {
//    requestAnimationFrame(() => {
      if (this.batchs.length) {
        update(this.batchs);
        this.batchs.length = 0;
        this.batchCallback && this.batchCallback();
        this.batchCallback = null;
      }
//    });
  }

  private drainRenderQueue() {
    const next = this.renderQueue.shift();
    if (next) {
      const {element, cb} = next;
      this.render(element, cb);
    }
  }

  public unmountComponent(fuelElement: FuelElement, cb: () => void) {
    cleanupTree(fuelElement, cb);
  }

  public render(el: FuelElement, callback: (el: FuelDOMNode) => void = (el => {}), context: any = {}, updateOwnwer = true) {
    if (!this._enabled) {
      callback(this.tree.dom as any);
      return;
    }

    if (this.lock) {
      this.renderQueue.push({element: el, cb: callback});
      return;
    }

    FuelStem.renderer.updateId();
    if (this.tree) {
      this.lock = true;
      this.patch(el, context);
      const old = this.tree;
      if (updateOwnwer) {
        this.tree = el;
      }
      this.batchCallback = () => {
        cleanupTree(old);
        callback(this.tree.dom as any);
        this.lock = false;
        this.drainRenderQueue();
      };
      this.renderAtAnimationFrame();
    } else {
      callback(this.attach(el, updateOwnwer) as any);
    }
  }


  private attach(el: FuelElement, updateOwner: boolean) {
    const domTree = fastCreateDomTree({}, el, el, FuelStem.renderer, createStem);
    if (updateOwner) {
      this.tree = el;
    }
    return domTree;
  }


  private patch(newTree: FuelElement, context) {
    if (this.batchs.length) {
      this.batchs.length = 0;
    }

    const stack = makeInitialStackState(context, newTree, this.tree);

    let parent: PatchStackType = null;

    while (stack.length) {
      const next = stack.pop();
      let {newElement, oldElement, context, isKeyedItem} = next;
      let difference: Difference;
      let currentRoot = next.root;

      if (!next.parsed) {

        [context, newElement, oldElement] = patchComponent(context, newElement, oldElement);

        if (!newElement && !oldElement) {
          continue;
        }

        if (newElement && oldElement) {
          newElement._stem = oldElement._stem;
        }

        next.newElement = newElement;
        next.oldElement = oldElement;
        next.context = context;

        if (newElement && newElement._stem) {
          currentRoot = next.newElement;
        }

        difference = diff(oldElement, newElement);
        next.difference = difference;

        if (oldElement) {
          invariant(!oldElement.dom, 'Dom element was accidentally removed.');
        }

        this.batchs.push({
          root: currentRoot,
          parent: parent? parent.newElement: null,
          newElement,
          oldElement,
          isKeyedItem,
          difference,
          context: next.context
        });

        next.newChildren = newElement? newElement.children.slice(): [];
        next.oldChildren = oldElement? oldElement.children.slice(): [];
        next.parsed = true;
      }

      if ((next.newChildren.length || next.oldChildren.length) &&
          (!next.difference ||
           next.difference.flags === 0 ||
           next.difference.flags === DifferenceBits.REPLACE_ELEMENT)) {
        stack.push(next);
        stack.push(createNextStackState(context, parent, next, oldElement));
        parent = next;
      }
    }
  }
}

/*
 * Timothy Deligero, Viktor Orlorvic, Cody Dailidonis
 * Course: COP6616 (Multicore Programming)
 * Project Assignment #2
 */

import java.io.*;
import java.util.*;
import java.util.concurrent.atomic.*;
import java.lang.*;

/*
 * A Node class used in the Vector class to represent the
 * elements within the memory storage. Contains a Generic
 * value.
 */
class Node<T>
{
	T val;
	
	// Class constructor.
	Node(T val)
	{
		this.val = val;
	}
	
}

/*
 * Contains an element to return a boolean value and a Node
 * elements from certain operations within the vector class.
 */
class Return_Elem<T>
{
	boolean check;
	Object val;
	
	// Class constructor.
	Return_Elem(boolean check, Object old_Elem)
	{
		this.check = check;
		this.val = old_Elem;
	}
}

/*
 * Contains the state of a Descriptor or an operation within 
 * the Vector's elements.
 */
enum State
{
	UNDECIDED,
	FAILED,
	PASSED;
}

/*
 * Contains the type of Descriptor used in the Vector's 
 * elements, being 1) Pop Descriptor, 2) Pop-sub Descriptor, 
 * 3) Push Descriptor, 4) WriteHelper Descriptor, and 5) Shift 
 * Descriptor. 
 */
enum Descr
{
	POP,
	POPSUB,
	PUSH,
	WRITE,
	SHIFT;
}

class PopDescr<T>
{
	Vector<T> vec;
	int pos;
	AtomicReference<Object> child = new AtomicReference<Object>();
	
	PopDescr(Vector<T> vec, int pos)
	{
		this.vec = vec;
		this.pos = pos;
		child.set(null);
	}
	
	@SuppressWarnings("unchecked")
	boolean complete()
	{
		int failures = 0;
		
		while(this.child.get() == null)
		{
			if(failures++ >= this.vec.limit)
			{
				this.child.compareAndSet(null, State.FAILED);
			}
			
			else
			{
				Object expected;
				
				if(!this.vec.segmented_contiguous)
				{
					SegSpot spot = this.vec.getSegSpot(this.pos - 1);
					expected = this.vec.segStorage.segments.get(spot.segIdx).get(spot.itemIdx);
					
					if(expected.equals(this.vec.NotValue_Elem))
					{
						this.child.compareAndSet(null, State.FAILED);
					}
					
					else if(expected instanceof Descriptor)
					{
						((Descriptor<T>) expected).complete();
					}
					
					else
					{
						PopSubDescr<T> psh = new PopSubDescr<T>(this, expected);
						
						if(this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, expected, psh))
						{
							this.child.compareAndSet(null, psh);
							
							if(this.child.get().equals(psh))
							{
								this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, psh, this.vec.NotValue_Elem);
							}
							
							else
							{
								this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, this, expected);
							}
						}
					}
				}
				
				else
				{
					int spot = this.vec.getConSpot(this.pos - 1);
					expected = this.vec.conStorage.array.get(spot).getReference();
					
					if(expected.equals(this.vec.NotValue_Elem))
					{
						this.child.compareAndSet(null, State.FAILED);
					}
					
					else if(expected instanceof Descriptor)
					{
						((Descriptor<T>) expected).complete();
					}
					
					else
					{
						PopSubDescr<T> psh = new PopSubDescr<T>(this, expected);
						
						if(this.vec.conStorage.array.get(spot).compareAndSet(expected, psh, false, false))
						{
							this.child.compareAndSet(null, psh);
							
							if(this.child.get().equals(psh))
							{
								this.vec.conStorage.array.get(spot).compareAndSet(psh, this.vec.NotValue_Elem, false, false);
							}
							
							else
							{
								this.vec.conStorage.array.get(spot).compareAndSet(this, expected, false, false);
							}
						}
					}
				}
			}	
		}
		
		if(!this.vec.segmented_contiguous)
		{
			SegSpot spot = this.vec.getSegSpot(this.pos);
			this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, this, this.vec.NotValue_Elem);
		}
		
		else
		{
			int spot = this.vec.getConSpot(this.pos);
			this.vec.conStorage.array.get(spot).compareAndSet(this, this.vec.NotValue_Elem, false, false);
		}
		
		return (!this.child.get().equals(State.FAILED));
	}
}

class PopSubDescr<T>
{
	PopDescr<T> parent;
	Node<T> value;
	
	@SuppressWarnings("unchecked")
	PopSubDescr(PopDescr<T> parent, Object value)
	{
		this.parent = parent;
		this.value = (Node<T>) value;
	}
	
	boolean complete()
	{
		if(!this.parent.vec.segmented_contiguous)
		{
			SegSpot spot = this.parent.vec.getSegSpot(this.parent.pos - 1);
			
			if(this.parent.child.get().equals(this))
			{
				this.parent.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, this, this.parent.vec.NotValue_Elem);
			}
			
			else
			{
				this.parent.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, this, this.value);
			}
		}
		
		else
		{
			int spot = this.parent.vec.getConSpot(this.parent.pos - 1);
			
			if(this.parent.child.get().equals(this))
			{
				this.parent.vec.conStorage.array.get(spot).compareAndSet(this, this.parent.vec.NotValue_Elem, false, false);
			}
			
			else
			{
				this.parent.vec.conStorage.array.get(spot).compareAndSet(this, this.value, false, false);
			}
		}
		
		return (this.parent.child.get().equals(this));
	}
}

class PushDescr<T>
{
	Vector<T> vec;
	Node<T> value;
	int pos;
	AtomicReference<State> state = new AtomicReference<State>();
	
	PushDescr(Vector<T> vec, Node<T> value, int pos)
	{
		this.vec = vec;
		this.value = value;
		this.pos = pos;
		this.state.set(State.UNDECIDED);
	}
	
	@SuppressWarnings("unchecked")
	boolean complete()
	{
		int failures = 0;
		Object current;
		
		if(!this.vec.segmented_contiguous)
		{
			SegSpot spot = this.vec.segStorage.getSpot(this.pos);
			SegSpot spot2 = this.vec.segStorage.getSpot(this.pos - 1);
			current = this.vec.segStorage.segments.get(spot2.segIdx).get(spot2.itemIdx);
			
			while(!(this.state.get().equals(State.UNDECIDED)) && (current instanceof Descriptor))
			{
				if(failures++ >= this.vec.limit)
				{
					this.state.compareAndSet(State.UNDECIDED, State.FAILED);
				}
				
				((Descriptor<T>) current).complete();
				current = this.vec.segStorage.segments.get(spot2.segIdx).get(spot2.itemIdx);
			}
			
			if(this.state.get().equals(State.UNDECIDED))
			{
				if(current.equals(this.vec.NotValue_Elem))
				{
					this.state.compareAndSet(State.UNDECIDED, State.FAILED);
				}
				
				else
				{
					this.state.compareAndSet(State.UNDECIDED, State.PASSED);
				}
			}
			
			if(this.state.get().equals(State.PASSED))
			{
				this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, this, this.value);
			}
			
			else
			{
				this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, this, this.vec.NotValue_Elem);
			}
		}
		
		else
		{
			int spot = this.vec.conStorage.getSpot(this.pos);
			int spot2 = this.vec.conStorage.getSpot(this.pos - 1);
			current = this.vec.conStorage.array.get(spot2).getReference();
			
			while(!(this.state.get().equals(State.UNDECIDED)) && (current instanceof Descriptor))
			{
				if(failures++ >= this.vec.limit)
				{
					this.state.compareAndSet(State.UNDECIDED, State.FAILED);
				}
				
				((Descriptor<T>) current).complete();
				current = this.vec.conStorage.array.get(spot2).getReference();
			}
			
			if(this.state.get().equals(State.UNDECIDED))
			{
				if(current.equals(this.vec.NotValue_Elem))
				{
					this.state.compareAndSet(State.UNDECIDED, State.FAILED);
				}
				
				else
				{
					this.state.compareAndSet(State.UNDECIDED, State.PASSED);
				}
			}
			
			if(this.state.get().equals(State.PASSED))
			{
				current = this.vec.conStorage.array.get(spot).compareAndSet(this, this.value, false, false);
			}
			
			else
			{
				current = this.vec.conStorage.array.get(spot).compareAndSet(this, this.vec.NotValue_Elem, false, false);
			}
		}
		
		return (this.state.get().equals(State.PASSED));
	}
}

class ShiftDescr<T>
{
	ShiftOp<T> op;
	int pos;
	Node<T> value;
	ShiftDescr<T> prev;
	AtomicReference<ShiftDescr<T>> next = new AtomicReference<ShiftDescr<T>>();
	
	ShiftDescr(ShiftOp<T> op, ShiftDescr<T> prev, Node<T> value, int pos)
	{
		this.op = op;
		this.pos = pos;
		this.value = value;
		this.prev = prev;
		this.next.set(null);
	}
	
	boolean complete()
	{
		boolean isAssoc = false;
		
		if(this.prev == null)
		{
			this.op.next.compareAndSet(null, this);
			isAssoc = this.op.next.get() == this;
		}
		
		else
		{
			this.prev.next.compareAndSet(null, this);
			isAssoc = this.prev.next.get() == this;
		}
		
		if(!this.op.vec.segmented_contiguous)
		{
			SegSpot spot = this.op.vec.getSegSpot(pos);
			
			if(isAssoc)
			{
				this.op.complete();
				this.op.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, this, this.op.valueGetter(this));
			}
			
			else
			{
				this.op.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, this, this.value);
			}
		}
		
		else
		{
			int spot = this.op.vec.getConSpot(pos);
			
			if(isAssoc)
			{
				this.op.complete();
				this.op.vec.conStorage.array.get(spot).compareAndSet(this, this.op.valueGetter(this), false, false);
			}
			
			else
			{
				this.op.vec.conStorage.array.get(spot).compareAndSet(this, this.value, false, false);
			}
		}
		
		return true;
	}
}

/*
 * Descriptor Object that contains a type of Descriptor Object used 
 * by the Vector class, including: 1) Pop Descriptor, 2) Pop-sub Descriptor, 
 * 3) Push Descriptor, and 4) Shift Descriptor. The type of Descriptor Object 
 * used will depend on which Constructor is used during the initialization of
 * the Descriptor Object. This class contains a complete() function to complete
 * the operation of the initialized Descriptor Object and a getValue() function
 * to get the Node value currently contained within the Descriptor.
 */
class Descriptor<T>
{
	// Fields containing the Descriptor type and different Descriptor Objects.
	Descr type;
	PopDescr<T> pop;
	PopSubDescr<T> popSub;
	PushDescr<T> push;
	WriteHelper<T> write;
	ShiftDescr<T> shift;
	
	// Constructor for a Pop Descriptor.
	Descriptor(Vector<T> vec, int pos)
	{
		type = Descr.POP;
		pop = new PopDescr<T>(vec, pos);
	}
	
	// Constructor for a Pop-sub Descriptor.
	Descriptor(PopDescr<T> parent, Node<T> value)
	{
		type = Descr.POPSUB;
		popSub = new PopSubDescr<T>(parent, value);
	}
	
	// Constructor for a Push Descriptor.
	Descriptor(Vector<T> vec, int pos, Node<T> value)
	{
		type = Descr.PUSH;
		push = new PushDescr<T>(vec, value, pos);
	}
	
	// Constructor for a WriteHelper Descriptor.
	Descriptor(WriteOp<T> parent, Node<T> value)
	{
		type = Descr.WRITE;
		write = new WriteHelper<T>(parent, value);
	}
	
	// Constructor for a Shift Descriptor.
	Descriptor(ShiftOp<T> op, ShiftDescr<T> prev, Node<T> value, int pos)
	{
		type = Descr.SHIFT;
		shift = new ShiftDescr<T>(op, prev, value, pos);
	}
	
	// Function that completes the Descriptor Object's operation.
	boolean complete()
	{
		if(type == Descr.POP)
		{
			return pop.complete();
		}
		
		else if(type == Descr.POPSUB)
		{
			return popSub.complete();
		}
		
		else if(type == Descr.PUSH)
		{
			return push.complete();
		}
		
		else if(type == Descr.WRITE)
		{
			return write.complete();
		}
		
		else if(type == Descr.SHIFT)
		{
			return shift.complete();
		}
		
		return false;
	}
	
	// Function that gets the Node value contained within the Descriptor Object.
	@SuppressWarnings("unchecked")
	Node<T> getValue()
	{
		if(type == Descr.POP)
		{
			return ((PopSubDescr<T>) pop.child.get()).value;
		}
		
		else if(type == Descr.POPSUB)
		{
			return popSub.value;
		}
		
		else if(type == Descr.PUSH)
		{
			return push.value;
		}
		
		else if(type == Descr.WRITE)
		{
			return write.value;
		}
		
		else if(type == Descr.SHIFT)
		{
			return shift.value;
		}
		
		return null;
	}
}

class WFPopOp<T>
{
	Vector<T> vec;
	
	WFPopOp(Vector<T> vec)
	{
		this.vec = vec;
	}
	
	@SuppressWarnings("unchecked")
	Return_Elem<T> helpComplete()
	{
		int pos = this.vec.size.get();
		
		if(pos == 0)
		{
			return new Return_Elem<T>(false, null);
		}
		
		if(!this.vec.segmented_contiguous)
		{
			SegSpot spot = this.vec.getSegSpot(pos);
			Object expected = this.vec.segStorage.segments.get(spot.segIdx).get(spot.itemIdx);
			
			if(expected.equals(this.vec.NotValue_Elem))
			{
				Descriptor<T> ph = new Descriptor<T>(this.vec, pos);
				
				if(this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, this.vec.NotValue_Elem, ph))
				{
					boolean res = ph.complete();
					
					if(res)
					{
						Object value = ph.pop.child.get();
						this.vec.size.getAndDecrement();
						return new Return_Elem<T>(true, value);
					}
					
					else
					{
						pos--;
					}
				}
			}
			
			else if(expected instanceof Descriptor)
			{
				((Descriptor<T>) expected).complete();
			}
		}
		
		else
		{
			int spot = this.vec.getConSpot(pos);
			Object expected = this.vec.conStorage.array.get(spot);
			
			if(expected.equals(this.vec.NotValue_Elem))
			{
				Descriptor<T> ph = new Descriptor<T>(this.vec, pos);
				
				if(this.vec.conStorage.array.get(spot).compareAndSet(this.vec.NotValue_Elem, ph, false, false))
				{
					boolean res = ph.complete();
					
					if(res)
					{
						Object value = ((PopSubDescr<T>) ph.pop.child.get()).value;
						this.vec.size.getAndDecrement();
						return new Return_Elem<T>(true, value);
					}
					
					else
					{
						pos--;
					}
				}
			}
			
			else if(expected instanceof Descriptor)
			{
				((Descriptor<T>) expected).complete();
			}
		}
		
		return new Return_Elem<T>(false, null);
	}
}

class WFPushOp<T>
{
	Vector<T> vec;
	Node<T> value;
	
	WFPushOp(Vector<T> vec, Node<T> value)
	{
		this.vec = vec;
		this.value = value;
	}
	
	@SuppressWarnings("unchecked")
	int helpComplete()
	{
		int pos = this.vec.size.get();
		
		if(!this.vec.segmented_contiguous)
		{
			SegSpot spot = this.vec.getSegSpot(pos);
			Object expected = this.vec.segStorage.segments.get(spot.segIdx).get(spot.itemIdx);
			
			if(expected.equals(this.vec.NotValue_Elem))
			{
				if(pos == 0)
				{
					if(this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, expected, value))
					{
						this.vec.size.getAndIncrement();
						return 0;
					}
					
					else
					{
						pos++;
						spot = this.vec.getSegSpot(pos);
					}
				}
			
				Descriptor<T> ph = new Descriptor<T>(this.vec, pos, value);
				
				if(this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, expected, ph))
				{
					boolean res = ph.push.complete();
					
					if(res)
					{
						this.vec.size.getAndIncrement();
						return pos - 1;
					}
					
					else
					{
						pos--;
					}
				}
				
				else if(expected instanceof Descriptor)
				{
					((Descriptor<T>) expected).complete();
				}
			}
			
			else if(expected instanceof Descriptor)
			{
				((Descriptor<T>) expected).complete();
			}
		}
		
		else
		{
			int spot = this.vec.getConSpot(pos);
			Object expected = this.vec.conStorage.array.get(spot);
			
			if(expected.equals(this.vec.NotValue_Elem))
			{
				if(pos == 0)
				{
					if(this.vec.conStorage.array.get(spot).compareAndSet(expected, value, false, false))
					{
						this.vec.size.getAndIncrement();
						return 0;
					}
					
					else
					{
						pos++;
						spot = this.vec.getConSpot(pos);
					}
				}
			
				Descriptor<T> ph = new Descriptor<T>(this.vec, pos, value);
				
				if(this.vec.conStorage.array.get(spot).compareAndSet(expected, ph, false, false))
				{
					boolean res = ph.push.complete();
					
					if(res)
					{
						this.vec.size.getAndIncrement();
						return pos - 1;
					}
					
					else
					{
						pos--;
					}
				}
				
				else if(expected instanceof Descriptor)
				{
					((Descriptor<T>) expected).complete();
				}
			}
			
			else if(expected instanceof Descriptor)
			{
				((Descriptor<T>) expected).complete();
			}
		}
		
		return 0;
	}
}

class CASPopOp<T>
{
	Vector<T> vec;
	
	CASPopOp(Vector<T> vec)
	{
		this.vec = vec;
	}
	
	Return_Elem<T> helpComplete()
	{
		int pos = this.vec.size.get() - 1;
		
		if(pos < 0)
		{
			return new Return_Elem<T>(false, null);
		}
		
		else
		{
			if(!this.vec.segmented_contiguous)
			{
				SegSpot spot = this.vec.getSegSpot(pos);
				Object cur = this.vec.segStorage.segments.get(spot.segIdx).get(spot.itemIdx);
				
				if(!cur.equals(this.vec.NotValue_Elem) && this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, cur, this.vec.NotValue_Elem))
				{
					this.vec.size.getAndDecrement();
					Object value = cur;
					return new Return_Elem<T>(true, value);
				}
			}
			
			else
			{
				int spot = this.vec.getConSpot(pos);
				Object cur = this.vec.conStorage.array.get(spot);
				
				if(!cur.equals(this.vec.NotValue_Elem) && this.vec.conStorage.array.get(spot).compareAndSet(cur, this.vec.NotValue_Elem, false, false))
				{
					this.vec.size.getAndDecrement();
					Object value = cur;
					return new Return_Elem<T>(true, value);
				}
			}
		}
		
		return new Return_Elem<T>(false, null);
	}
}

class CASPushOp<T>
{
	Vector<T> vec;
	Node<T> value;
	
	CASPushOp(Vector<T> vec, Node<T> value)
	{
		this.vec = vec;
		this.value = value;
	}
	
	int helpComplete()
	{
		int pos = this.vec.size.get();
			
		if(!this.vec.segmented_contiguous)
		{
			SegSpot spot = this.vec.getSegSpot(pos);
			Object cur = this.vec.segStorage.segments.get(spot.segIdx).get(spot.itemIdx);
			
			if(cur.equals(this.vec.NotValue_Elem) && this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, cur, value))
			{
				this.vec.size.getAndIncrement();
				return pos;
			}
		}
		
		else
		{
			int spot = this.vec.getConSpot(pos);
			Object cur = this.vec.conStorage.array.get(spot);
			
			if(cur.equals(this.vec.NotValue_Elem) && this.vec.conStorage.array.get(spot).compareAndSet(cur, value, false, false))
			{
				this.vec.size.getAndIncrement();
				return pos;
			}
		}
		
		return 0;
	}
}

class WriteOp<T>
{
	Vector<T> vec;
	int pos;
	Object old_Elem;
	Object new_Elem;
	AtomicReference<WriteHelper<T>> child = new AtomicReference<WriteHelper<T>>();
	
	WriteOp(Vector<T> vec, int pos, Object old_Elem, Object new_Elem)
	{
		this.vec= vec;
		this.pos = pos;
		this.old_Elem = old_Elem;
		this.new_Elem = new_Elem;
		this.child.set(null);
	}
	
	@SuppressWarnings("unchecked")
	Return_Elem<T> helpComplete()
	{
		if(!this.vec.segmented_contiguous)
		{
			SegSpot spot = this.vec.getSegSpot(this.pos);
			Object value = this.vec.segStorage.segments.get(spot.segIdx).get(spot.itemIdx);
			
			if(value instanceof Descriptor)
			{
				((Descriptor<T>) value).complete();
			}
			
			else
			{
				WriteHelper<T> write = new WriteHelper<T>(this, (Node<T>) value);
				
				if(this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, value, write))
				{
					this.child.compareAndSet(null, write);
					
					if(this.child.get().equals(write))
					{
						Node<T> currentValue = write.value;
						
						if(currentValue.equals(old_Elem))
						{
							this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, write, new_Elem);
						}
						
						else
						{
							this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, write, currentValue);
						}
					}
				}
			}
		}
		
		else
		{
			int spot = this.vec.getConSpot(this.pos);
			Object value = this.vec.conStorage.array.get(spot).getReference();
			
			if(value instanceof Descriptor)
			{
				((Descriptor<T>) value).complete();
			}
			
			else
			{
				WriteHelper<T> write = new WriteHelper<T>(this, (Node<T>) value);
				
				if(this.vec.conStorage.array.get(spot).compareAndSet(value, write, false, false))
				{
					this.child.compareAndSet(null, write);
					
					if(this.child.get().equals(write))
					{
						Node<T> currentValue = write.value;
						
						if(currentValue.equals(old_Elem))
						{
							this.vec.conStorage.array.get(spot).compareAndSet(write, new_Elem, false, false);
						}
						
						else
						{
							this.vec.conStorage.array.get(spot).compareAndSet(write, currentValue, false, false);
						}
					}
				}
			}
		}
		
		return new Return_Elem<T>(false, null);
	}
}

class WriteHelper<T>
{
	WriteOp<T> parent;
	Node<T> value;
	
	WriteHelper(WriteOp<T> parent, Node<T> value)
	{
		this.parent = parent;
		this.value = value;
	}
	
	boolean complete()
	{
		if(!this.parent.vec.segmented_contiguous)
		{
			SegSpot spot = this.parent.vec.getSegSpot(this.parent.pos);
			
			if(this.parent.child.get().equals(this) && this.value.equals(this.parent.old_Elem))
			{
				this.parent.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, this, this.parent.new_Elem);
			}
			
			else
			{
				this.parent.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, this, this.value);
			}
		}
		
		else
		{
			int spot = this.parent.vec.getConSpot(this.parent.pos);
			
			if(this.parent.child.get().equals(this) && this.value.equals(this.parent.old_Elem))
			{
				this.parent.vec.conStorage.array.get(spot).compareAndSet(this, this.parent.new_Elem, false, false);
			}
			
			else
			{
				this.parent.vec.conStorage.array.get(spot).compareAndSet(this, this.value, false, false);
			}
		}
		
		return (this.parent.child.get().equals(this));
	}
}

class ShiftOp<T>
{
	Vector<T> vec;
	int pos;
	AtomicBoolean incomplete = new AtomicBoolean();
	AtomicReference<Object> next = new AtomicReference<Object>();
	
	boolean shiftType;
	Node<T> value;
	
	ShiftOp(Vector<T> vec, int pos, boolean shiftType, Node<T> value)
	{
		this.vec = vec;
		this.pos = pos;
		this.incomplete.set(true);
		this.next.set(null);
		
		this.shiftType = shiftType;
		this.value = value;
	}
	
	ShiftOp(ShiftOp<T> shift)
	{
		this.vec = shift.vec;
		this.pos = shift.pos;
		this.incomplete.set(true);
		this.next.set(null);
		
		this.shiftType = shift.shiftType;
		this.value = shift.value;
	}
	
	@SuppressWarnings("unchecked")
	void complete()
	{
		int i = this.pos;
		
		if(i >= this.vec.getCapacity())
		{
			this.next.compareAndSet(null, State.FAILED);
		}
		
		int failures = 0;
		
		while(this.next.get() == null)
		{
			if(failures++ == this.vec.limit)
			{
				this.vec.announceShiftOp(this);
				return;
			}
			
			Object cvalue;
			
			if(!this.vec.segmented_contiguous)
			{
				SegSpot spot = this.vec.segStorage.getSpot(this.pos);
				cvalue = this.vec.segStorage.segments.get(spot.segIdx).get(spot.itemIdx);
				
				if(cvalue instanceof Descriptor)
				{
					((Descriptor<T>) cvalue).complete();
				}
				
				else if(cvalue.equals(this.vec.NotValue_Elem))
				{
					this.next.compareAndSet(null, State.FAILED);
				}
				
				else
				{
					Descriptor<T> sh = new Descriptor<T>(this, null, (Node<T>) cvalue, i);
					
					if(this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, cvalue, sh))
					{
						this.next.compareAndSet(null, sh);
						
						if(!(sh.equals(this.next.get())))
						{
							this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, sh, cvalue);
						}
					}
				}
			}
			
			else
			{
				int spot = this.vec.conStorage.getSpot(this.pos);
				cvalue = this.vec.conStorage.array.get(spot).getReference();
				
				if(cvalue instanceof Descriptor)
				{
					((Descriptor<T>) cvalue).complete();
				}
				
				else if(cvalue.equals(this.vec.NotValue_Elem))
				{
					this.next.compareAndSet(null, State.FAILED);
				}
				
				else
				{
					Descriptor<T> sh = new Descriptor<T>(this, null, (Node<T>) cvalue, i);
					
					if(this.vec.conStorage.array.get(spot).compareAndSet(cvalue, sh, false, false))
					{
						this.next.compareAndSet(null, sh);
						
						if(!(sh.equals(this.next.get())))
						{
							this.vec.conStorage.array.get(spot).compareAndSet(sh, cvalue, false, false);
						}
					}
				}
			}
		}
		
		Object last = this.next.get();
		
		if(last.equals(State.FAILED))
		{
			return;
		}
		
		while(this.incomplete.get())
		{
			i++;
			
			if(((Descriptor<T>) last).shift.value == null)
			{
				this.incomplete.set(false);
			}
			
			failures = 0;
			
			while(((Descriptor<T>) last).shift.next.get() == null)
			{
				if(failures++ == this.vec.limit)
				{
					this.vec.announceShiftOp(this);
					return;
				}
				
				Object cvalue;
				
				if(!this.vec.segmented_contiguous)
				{
					SegSpot spot = this.vec.segStorage.getSpot(this.pos);
					cvalue = this.vec.segStorage.segments.get(spot.segIdx).get(spot.itemIdx);
					
					if(cvalue instanceof Descriptor)
					{
						if(((Descriptor<T>) cvalue).type.equals(Descr.PUSH))
						{
							((Descriptor<T>) cvalue).push.state.compareAndSet(State.UNDECIDED, State.PASSED);
						}
						
						else if(((Descriptor<T>) cvalue).type.equals(Descr.POP))
						{
							((Descriptor<T>) cvalue).pop.child.compareAndSet(null, State.FAILED);
						}
						
						((Descriptor<T>) cvalue).complete();
					}
					
					else
					{
						Descriptor<T> sh = new Descriptor<T>(this, ((Descriptor<T>) last).shift, (Node<T>) cvalue, i);
						
						if(this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, cvalue, sh))
						{
							((Descriptor<T>) last).shift.next.compareAndSet(null, sh.shift);
							
							if(!(sh.shift.equals(((Descriptor<T>) last).shift.next.get())))
							{
								this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, sh, cvalue);
							}
						}
					}
				}
				
				else
				{
					int spot = this.vec.conStorage.getSpot(this.pos);
					cvalue = this.vec.conStorage.array.get(spot).getReference();
					
					if(cvalue instanceof Descriptor)
					{
						if(((Descriptor<T>) cvalue).type.equals(Descr.PUSH))
						{
							((Descriptor<T>) cvalue).push.state.compareAndSet(State.UNDECIDED, State.PASSED);
						}
						
						else if(((Descriptor<T>) cvalue).type.equals(Descr.POP))
						{
							((Descriptor<T>) cvalue).pop.child.compareAndSet(null, State.FAILED);
						}
						
						((Descriptor<T>) cvalue).complete();
					}
					
					else
					{
						Descriptor<T> sh = new Descriptor<T>(this, ((Descriptor<T>) last).shift, (Node<T>) cvalue, i);
						
						if(this.vec.conStorage.array.get(spot).compareAndSet(cvalue, sh, false, false))
						{
							((Descriptor<T>) last).shift.next.compareAndSet(null, sh.shift);
							
							if(!(sh.shift.equals(((Descriptor<T>) last).shift.next.get())))
							{
								this.vec.conStorage.array.get(spot).compareAndSet(sh, cvalue, false, false);
							}
						}
					}
				}
			}
			
			ShiftDescr<T> newShift = ((Descriptor<T>) last).shift.next.get();

			last = new Descriptor<T>(newShift.op, newShift.prev, newShift.value, newShift.pos);
		}
	}
	
	@SuppressWarnings("unchecked")
	void helpComplete()
	{
		int i = this.pos;
		
		if(i >= this.vec.getCapacity())
		{
			this.next.compareAndSet(null, State.FAILED);
		}
		
		while(this.next.get() == null)
		{
			Object cvalue;
			
			if(!this.vec.segmented_contiguous)
			{
				SegSpot spot = this.vec.segStorage.getSpot(this.pos);
				cvalue = this.vec.segStorage.segments.get(spot.segIdx).get(spot.itemIdx);
				
				if(cvalue instanceof Descriptor)
				{
					((Descriptor<T>) cvalue).complete();
				}
				
				else if(cvalue.equals(this.vec.NotValue_Elem))
				{
					this.next.compareAndSet(null, State.FAILED);
				}
				
				else
				{
					Descriptor<T> sh = new Descriptor<T>(this, null, (Node<T>) cvalue, i);
					
					if(this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, cvalue, sh))
					{
						this.next.compareAndSet(null, sh);
						
						if(!(sh.equals(this.next.get())))
						{
							this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, sh, cvalue);
						}
					}
				}
			}
			
			else
			{
				int spot = this.vec.conStorage.getSpot(this.pos);
				cvalue = this.vec.conStorage.array.get(spot).getReference();
				
				if(cvalue instanceof Descriptor)
				{
					((Descriptor<T>) cvalue).complete();
				}
				
				else if(cvalue.equals(this.vec.NotValue_Elem))
				{
					this.next.compareAndSet(null, State.FAILED);
				}
				
				else
				{
					Descriptor<T> sh = new Descriptor<T>(this, null, (Node<T>) cvalue, i);
					
					if(this.vec.conStorage.array.get(spot).compareAndSet(cvalue, sh, false, false))
					{
						this.next.compareAndSet(null, sh);
						
						if(!(sh.equals(this.next.get())))
						{
							this.vec.conStorage.array.get(spot).compareAndSet(sh, cvalue, false, false);
						}
					}
				}
			}
		}
		
		Object last = this.next.get();
		
		if(last.equals(State.FAILED))
		{
			return;
		}
		
		while(this.incomplete.get())
		{
			i++;
			
			if(((Descriptor<T>) last).shift.value == null)
			{
				this.incomplete.set(false);
			}
			
			while(((Descriptor<T>) last).shift.next.get() == null)
			{
				Object cvalue;
				
				if(!this.vec.segmented_contiguous)
				{
					SegSpot spot = this.vec.segStorage.getSpot(this.pos);
					cvalue = this.vec.segStorage.segments.get(spot.segIdx).get(spot.itemIdx);
					
					if(cvalue instanceof Descriptor)
					{
						if(((Descriptor<T>) cvalue).type.equals(Descr.PUSH))
						{
							((Descriptor<T>) cvalue).push.state.compareAndSet(State.UNDECIDED, State.PASSED);
						}
						
						else if(((Descriptor<T>) cvalue).type.equals(Descr.POP))
						{
							((Descriptor<T>) cvalue).pop.child.compareAndSet(null, State.FAILED);
						}
						
						((Descriptor<T>) cvalue).complete();
					}
					
					else
					{
						Descriptor<T> sh = new Descriptor<T>(this, ((Descriptor<T>) last).shift, (Node<T>) cvalue, i);
						
						if(this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, cvalue, sh))
						{
							((Descriptor<T>) last).shift.next.compareAndSet(null, sh.shift);
							
							if(!(sh.shift.equals(((Descriptor<T>) last).shift.next.get())))
							{
								this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, sh, cvalue);
							}
						}
					}
				}
				
				else
				{
					int spot = this.vec.conStorage.getSpot(this.pos);
					cvalue = this.vec.conStorage.array.get(spot).getReference();
					
					if(cvalue instanceof Descriptor)
					{
						if(((Descriptor<T>) cvalue).type.equals(Descr.PUSH))
						{
							((Descriptor<T>) cvalue).push.state.compareAndSet(State.UNDECIDED, State.PASSED);
						}
						
						else if(((Descriptor<T>) cvalue).type.equals(Descr.POP))
						{
							((Descriptor<T>) cvalue).pop.child.compareAndSet(null, State.FAILED);
						}
						
						((Descriptor<T>) cvalue).complete();
					}
					
					else
					{
						Descriptor<T> sh = new Descriptor<T>(this, ((Descriptor<T>) last).shift, (Node<T>) cvalue, i);
						
						if(this.vec.conStorage.array.get(spot).compareAndSet(cvalue, sh, false, false))
						{
							((Descriptor<T>) last).shift.next.compareAndSet(null, sh.shift);
							
							if(!(sh.shift.equals(((Descriptor<T>) last).shift.next.get())))
							{
								this.vec.conStorage.array.get(spot).compareAndSet(sh, cvalue, false, false);
							}
						}
					}
				}
			}
			
			ShiftDescr<T> newShift = ((Descriptor<T>) last).shift.next.get();

			last = new Descriptor<T>(newShift.op, newShift.prev, newShift.value, newShift.pos);
		}
	}
	
	@SuppressWarnings("unchecked")
	void clean()
	{
		ShiftDescr<T> sh = (ShiftDescr<T>) this.next.get();
		
		for(int tpos = this.pos; sh != null; tpos++)
		{
			if(!this.vec.segmented_contiguous)
			{
				SegSpot spot = this.vec.getSegSpot(tpos);
				this.vec.segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, sh, sh.value);
			}
			
			else
			{
				int spot = this.vec.getConSpot(tpos);
				this.vec.conStorage.array.get(spot).compareAndSet(sh, sh.value, false, false);
			}
			
			sh = sh.next.get();
		}
	}
	
	Node<T> valueGetter(ShiftDescr<T> sh)
	{
		if(!shiftType)
		{
			if(sh.prev == null)
			{
				return value;
			}
			
			else
			{
				return sh.prev.value;
			}
		}
		
		else
		{
			if(sh.next.get() == null)
			{
				return null;
			}
			
			else
			{
				return sh.next.get().value;
			}
		}
	}
}

class AnnouncementTable
{
	
}

/*
 * Contains a position of an element within a Segmented Element
 * Model. Contains both the segment index and the item index.
 */
class SegSpot
{
	int segIdx;
	int itemIdx;
	
	SegSpot(int segIdx, int itemIdx)
	{
		this.segIdx = segIdx;
		this.itemIdx = itemIdx;
	}
}

/*
 * Class containing segmented memory for the storage of elements for 
 * the Vector class. This model has memory stored in a list of segments, 
 * allowing threads to append a new array segment to the list during 
 * resizing,  without having to copy elements over a new array. A thread 
 * will access the list in order to access an element with the given position.
 */
class Segmented<T>
{
	/*
	 * Fields containing the initial capacity when the class is
	 * first initialized and the current capacity to keep in check
	 * of the capacity after the memory storage has been expanded.
	 */
	int initialCapacity;
	AtomicInteger currentCapacity = new AtomicInteger();
	Vector<T> vec;
	
	// Contains the list of array segments containing the memory storage.
	AtomicReferenceArray<AtomicReferenceArray<Object>> segments = new AtomicReferenceArray<AtomicReferenceArray<Object>>(100000);
	
	/*
	 * In the constructor, when given a capacity, have the initial and
	 * current be the power of 2 of the given capacity, such that the
	 * length of the first array segment is of 2^Y, where Y is the given
	 * capacity at the constructor. Add the first array segment with the
	 * current capacity.
	 */
	Segmented(Vector<T> vec, int capacity)
	{
		this.vec = vec;
		initialCapacity = capacity;
		currentCapacity.set(capacity);
		segments.set(0, new AtomicReferenceArray<Object>(currentCapacity.get()));
		
		for(int i = 0; i < currentCapacity.get(); i++)
		{
			segments.get(0).set(i, this.vec.NotValue_Elem);;
		}
	}
	
	/*
	 * Algorithm 1: Using bitwise operations, the address of an elements
	 * can be obtained from the memory storage's list of segments.
	 */
	SegSpot getSpot(int rawpos)
	{
		/*
		 * Use the given raw position from a thread to get the segment ID and
		 * item ID locations within the list of segments.
		 */
		int pos = rawpos + this.initialCapacity;
		int itemIdx = pos ^ (1 << ((int) Math.floor(Math.log(pos) / Math.log(2))));
		int segmentIdx = ((int) Math.floor(Math.log(pos) / Math.log(2)) - ((int) Math.floor(Math.log(this.initialCapacity) / Math.log(2))));
		
		// Obtain the array containing the requested element.
		AtomicReferenceArray<Object> array = this.segments.get(segmentIdx);
		
		/*
		 * If the array is NULL, meaning that the memory storage has not
		 * been resized to given position, expand the list of segments
		 * with the given segment ID.
		 */
		if(array == null)
		{
			array = this.expand(segmentIdx);
		}
		
		return new SegSpot(segmentIdx, itemIdx);
	}
	
	/*
	 * Algorithm 2: Expand the array up to the given segment ID using bitwise
	 * operations.
	 */
	AtomicReferenceArray<Object> expand(int segIdx)
	{
		AtomicReferenceArray<Object> array = this.segments.get(segIdx);
		
		// Check first if the given array segment is NULL before expanding.
		if(array == null)
		{
			// Get the new capacity using bitwise operations and being a power of 2.
			int newCapacity = (1 << ((int) Math.floor(Math.log(this.initialCapacity) / Math.log(2))) + segIdx);
			AtomicReferenceArray<Object> newArray = new AtomicReferenceArray<Object>(newCapacity);
			
			for(int i = 0; i < newCapacity; i++)
			{
				newArray.set(i, vec.NotValue_Elem);
			}
			
			if(segments.compareAndSet(segIdx, null, newArray))
			{
				this.currentCapacity.getAndAdd(newCapacity);
				return newArray;
			}
			
			// Return the newly created array segment.
			return this.segments.get(segIdx);
		}
		
		// If the array segment is not NULL, then just return the segment itself.
		return array;
	}
}

/*
 * Class containing contiguous memory for the storage of elements for the
 * Vector class. This model has memory stored into an array of elements as
 * well as into the arrays of referenced old Contiguous objects. When resized,
 * the elements are copied over to a new array with twice the current capacity.
 */
class Contiguous<T>
{
	/*
	 * Fields containing the current capacity, reference to the old Contiguous
	 * object, reference to the vector class containing the Contiguous storage,
	 * and the array of elements in memory.
	 */
	int capacity;
	Contiguous<T> old;
	Vector<T> vec;
	AtomicReferenceArray<AtomicMarkableReference<Object>> array;
	
	// In the constructor, initialize the field within the Contiguous object.
	Contiguous(Vector<T> vec, Contiguous<T> old, int capacity)
	{
		this.capacity = capacity;
		this.old = old;
		this.vec = vec;
		array = new AtomicReferenceArray<AtomicMarkableReference<Object>>(capacity);
		
		for(int i = 0; i < this.capacity; i++)
		{
			array.set(i, new AtomicMarkableReference<Object>(this.vec.NotValue_Elem, false));
		}
	}
	
	/*
	 * Algorithm 3: When a thread attempts to resize the memory storage, it
	 * allocates a new Contiguous object with twice the capacity and a reference
	 * to the current Contiguous object. All elements up to the previous capacity
	 * are initialized as NotCopied, while the rest are initialized to NotValue.
	 * The elements from the old Contiguous object's array are copied onto the
	 * new Contiguous object's array.
	 */
	Contiguous<T> resize()
	{
		/*
		 * Create a new Contiguous object with twice the capacity. Have elements 
		 * up to the previous capacity initialized as NotCopied, while the rest 
		 * are initialized to NotValue.
		 */
		Contiguous<T> vnew = new Contiguous<T>(this.vec, this, this.capacity * 2);
		
		for(int i = 0; i < this.capacity; i++)
		{
			vnew.array.set(i, new AtomicMarkableReference<Object>(this.vec.NotCopied_Elem, false));
		}
		
		for(int i = this.capacity; i < array.length(); i++)
		{
			vnew.array.set(i, new AtomicMarkableReference<Object>(this.vec.NotValue_Elem, false));
		}
		
		// Check if the current Contiguous object is the same as the old reference.
		if(this.vec.conStorage.equals(this))
		{
			// If so, copy all elements from the old reference into the new array.
			for(int i = this.capacity - 1; i >= 0; i--)
			{
				vnew.copyValue(i);
			}
			
			// Initialize the Vector class's Contiguous object with the new one.
			this.vec.conStorage = vnew;
		}
		
		// Return the current Contiguous object of the vector.
		return this.vec.conStorage;
	}
	
	/*
	 * Algorithm 4: Copies the values from the old Contiguous object's array
	 * into the current Contiguous object;s array of elements.
	 */
	void copyValue(int pos)
	{
		//System.out.println(pos);
		/*
		 * Check first if the value of the element is NotCopied, signifying
		 * that the position hasn't had the element copied over the position.
		 */
		if(this.old.array.get(pos).equals(this.vec.NotCopied_Elem))
		{
			// Copy the element into the position of the array.
			this.old.copyValue(pos);
		}
		
		Object v = this.old.array.get(pos).getReference();
		
		// Set the resize bit of the Node element to true or 1.
		this.old.array.get(pos).attemptMark(v, true);
		
		this.array.get(pos).compareAndSet(this.vec.NotCopied_Elem, v, false, false);
	}
	
	/*
	 * Algorithm 5: Get the element from the current Contiguous object's
	 * array at the given position.
	 */
	int getSpot(int pos)
	{
		/*
		 * If the position given is greater then the current capacity, then
		 * use the resize() operation to allocate a new Contiguous object,
		 * then get the element within the given position of the new array.
		 */
		if(pos >= this.capacity)
		{
			Contiguous<T> newArray = this.resize();
			return newArray.getSpot(pos);
		}
		
		/*
		 * If a thread sees that the position of the array is NotCopied, then
		 * copy the value from the old referenced Contiguous object.
		 */
		if(this.array.get(pos).equals(this.vec.NotCopied_Elem))
		{
			this.copyValue(pos);
		}
		
		// Return the element of the Contiguous object's array with the given position.
		return pos;
	}
}

/*
 * A wait-free vector class containing an internal storage, being either segmented
 * or contiguous, the current size, and utilizes tail operations, random access 
 * operations, and multi-position operations.
 */
class Vector<T>
{
	/*
	 * Fields containing a Segmented or Contiguous internal storage, the size,
	 * and the boolean value to represent which type of internal storage is
	 * used for the current Vector class.
	 */
	Segmented<T> segStorage;
	Contiguous<T> conStorage;
	AtomicInteger size = new AtomicInteger();
	boolean segmented_contiguous;
	
	/*
	 * Contains the values and elements for the NotCopied and NotValue
	 * to be used for the operations of the Vector class.
	 */
	int NotCopied = Integer.MIN_VALUE;
	int NotValue = Integer.MAX_VALUE;
	Node<Integer> NotCopied_Elem = new Node<Integer>(NotCopied);
	Node<Integer> NotValue_Elem = new Node<Integer>(NotValue);
	
	// Contains the limit of failures when a thread attempts to do an operation.
	int limit = 1000;
	
	/*
	 * In the constructor, a boolean value is given to signify which type of
	 * internal storage to use for the vector class. Initialize the internal
	 * storage with the given capacity and set the current size of the Vector
	 * to be 0.
	 */
	Vector(boolean segmented_contiguous, int capacity)
	{
		this.segmented_contiguous = segmented_contiguous;
		
		if(!segmented_contiguous)
		{
			segStorage = new Segmented<T>(this, capacity);
		}
		
		else
		{
			conStorage = new Contiguous<T>(this, null, capacity);
		}
		
		size.set(0);
	}
	
	/*
	 * Function within the Vector class to get the capacity of the Vector's
	 * internal storage. First, it is checked which type of storage is used 
	 * before getting the capacity.
	 */
	int getCapacity()
	{
		if(!segmented_contiguous)
		{
			return segStorage.currentCapacity.get();
		}

		return conStorage.capacity;
	}
	
	// Gets the position of an element within a Segmented Element Model.
	SegSpot getSegSpot(int pos)
	{
		return segStorage.getSpot(pos);
	}
	
	// Gets the position of an element within a Contiguous Element Model.
	int getConSpot(int pos)
	{
		return conStorage.getSpot(pos);
	}
	
	Return_Elem<T> announceWFPopOp(WFPopOp<T> operation)
	{
		return operation.helpComplete();
	}
	
	int announceWFPushOp(WFPushOp<T> operation)
	{
		return operation.helpComplete();
	}
	
	Return_Elem<T> announceCASPopOp(CASPopOp<T> operation)
	{
		return operation.helpComplete();
	}
	
	int announceCASPushOp(CASPushOp<T> operation)
	{
		return operation.helpComplete();
	}
	
	Return_Elem<T> announceWriteOp(WriteOp<T> operation)
	{
		return operation.helpComplete();
	}
	
	void announceShiftOp(ShiftOp<T> operation)
	{
		operation.helpComplete();
	}

	/*
	 * Algorithm 6: 
	 */
	@SuppressWarnings("unchecked")
	Return_Elem<T> WF_popBack()
	{
		int pos = this.size.get();
		
		for(int failures = 0; failures <= limit; failures++)
		{
			if(pos == 0)
			{
				return new Return_Elem<T>(false, null);
			}
			
			if(!segmented_contiguous)
			{
				SegSpot spot = getSegSpot(pos);
				Object expected = segStorage.segments.get(spot.segIdx).get(spot.itemIdx);
				
				if(expected.equals(NotValue_Elem))
				{
					Descriptor<T> ph = new Descriptor<T>(this, pos);
					
					if(segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, NotValue_Elem, ph))
					{
						boolean res = ph.complete();
						
						if(res)
						{
							Object value = ph.pop.child.get();
							this.size.getAndDecrement();
							return new Return_Elem<T>(true, value);
						}
						
						else
						{
							pos--;
						}
					}
				}
				
				else if(expected instanceof Descriptor)
				{
					((Descriptor<T>) expected).complete();
				}
				
				else
				{
					pos++;
				}
			}
			
			else
			{
				int spot = getConSpot(pos);
				Object expected = conStorage.array.get(spot);
				
				if(expected.equals(NotValue_Elem))
				{
					Descriptor<T> ph = new Descriptor<T>(this, pos);
					
					if(conStorage.array.get(spot).compareAndSet(NotValue_Elem, ph, false, false))
					{
						boolean res = ph.complete();
						
						if(res)
						{
							Object value = ((PopSubDescr<T>) ph.pop.child.get()).value;
							this.size.getAndDecrement();
							return new Return_Elem<T>(true, value);
						}
						
						else
						{
							pos--;
						}
					}
				}
				
				else if(expected instanceof Descriptor)
				{
					((Descriptor<T>) expected).complete();
				}
				
				else
				{
					pos++;
				}
			}
		}
		
		return announceWFPopOp(new WFPopOp<T>(this));
	}
	
	/*
	 * Algorithm 9:
	 */
	@SuppressWarnings("unchecked")
	int WF_pushBack(Node<T> value)
	{
		int pos = this.size.get();
		
		for(int failures = 0; failures <= limit; failures++)
		{
			if(!segmented_contiguous)
			{
				SegSpot spot = getSegSpot(pos);
				Object expected = segStorage.segments.get(spot.segIdx).get(spot.itemIdx);
				
				if(expected.equals(NotValue_Elem))
				{
					if(pos == 0)
					{
						if(segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, expected, value))
						{
							this.size.getAndIncrement();
							return 0;
						}
						
						else
						{
							pos++;
							spot = getSegSpot(pos);
						}
					}
				
					Descriptor<T> ph = new Descriptor<T>(this, pos, value);
					
					if(segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, expected, ph))
					{
						boolean res = ph.push.complete();
						
						if(res)
						{
							this.size.getAndIncrement();
							return pos - 1;
						}
						
						else
						{
							pos--;
						}
					}
					
					else if(expected instanceof Descriptor)
					{
						((Descriptor<T>) expected).complete();
					}
				}
				
				else if(expected instanceof Descriptor)
				{
					((Descriptor<T>) expected).complete();
				}
				
				else
				{
					pos++;
				}
			}
			
			else
			{
				int spot = getConSpot(pos);
				Object expected = conStorage.array.get(spot);
				
				if(expected.equals(NotValue_Elem))
				{
					if(pos == 0)
					{
						if(conStorage.array.get(spot).compareAndSet(expected, value, false, false))
						{
							this.size.getAndIncrement();
							return 0;
						}
						
						else
						{
							pos++;
							spot = getConSpot(pos);
						}
					}
				
					Descriptor<T> ph = new Descriptor<T>(this, pos, value);
					
					if(conStorage.array.get(spot).compareAndSet(expected, ph, false, false))
					{
						boolean res = ph.push.complete();
						
						if(res)
						{
							this.size.getAndIncrement();
							return pos - 1;
						}
						
						else
						{
							pos--;
						}
					}
					
					else if(expected instanceof Descriptor)
					{
						((Descriptor<T>) expected).complete();
					}
				}
				
				else if(expected instanceof Descriptor)
				{
					((Descriptor<T>) expected).complete();
				}
				
				else
				{
					pos++;
				}
			}
		}
		
		return announceWFPushOp(new WFPushOp<T>(this, value));
	}
	
	Return_Elem<T> CAS_popBack()
	{
		int pos = this.size.get() - 1;
		int failures = 0;
		
		while(true)
		{
			if(failures++ > limit)
			{
				return announceCASPopOp(new CASPopOp<T>(this));
			}
			
			else if(pos < 0)
			{
				return new Return_Elem<T>(false, null);
			}
			
			else
			{
				if(!segmented_contiguous)
				{
					SegSpot spot = getSegSpot(pos);
					Object cur = segStorage.segments.get(spot.segIdx).get(spot.itemIdx);
					
					if(!cur.equals(NotValue_Elem) && segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, cur, NotValue_Elem))
					{
						this.size.getAndDecrement();
						Object value = cur;
						return new Return_Elem<T>(true, value);
					}
					
					pos--;
				}
				
				else
				{
					int spot = getConSpot(pos);
					Object cur = conStorage.array.get(spot);
					
					if(!cur.equals(NotValue_Elem) && conStorage.array.get(spot).compareAndSet(cur, NotValue_Elem, false, false))
					{
						this.size.getAndDecrement();
						Object value = cur;
						return new Return_Elem<T>(true, value);
					}
					
					pos--;
				}
			}
		}
	}
	
	int CAS_pushBack(Node<T> value)
	{
		int pos = this.size.get();
		int failures = 0;
		
		while(true)
		{
			if(failures++ > limit)
			{
				return announceCASPushOp(new CASPushOp<T>(this, value));
			}
			
			if(!segmented_contiguous)
			{
				SegSpot spot = getSegSpot(pos);
				Object cur = segStorage.segments.get(spot.segIdx).get(spot.itemIdx);
				
				if(cur.equals(NotValue_Elem) && segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, cur, value))
				{
					this.size.getAndIncrement();
					return pos;
				}
				
				pos++;
			}
			
			else
			{
				int spot = getConSpot(pos);
				Object cur = conStorage.array.get(spot);
				
				if(cur.equals(NotValue_Elem) && conStorage.array.get(spot).compareAndSet(cur, value, false, false))
				{
					this.size.getAndIncrement();
					return pos;
				}
				
				pos++;
			}
		}
	}
	
	/*
	 * Algorithm 13: 
	 */
	Return_Elem<T> FAA_popBack()
	{
		int pos = this.size.getAndDecrement() - 1;
		
		if(pos >= 0)
		{
			if(!segmented_contiguous)
			{
				SegSpot spot = getSegSpot(pos);
				Object value = segStorage.segments.get(spot.segIdx).get(spot.itemIdx);
				segStorage.segments.get(spot.segIdx).set(spot.itemIdx, NotValue_Elem);
				return new Return_Elem<T>(true, value);
			}
			
			else
			{
				int spot = getConSpot(pos);
				Object value = conStorage.array.get(spot).getReference();
				conStorage.array.get(spot).set(NotValue_Elem, false);
				return new Return_Elem<T>(true, value);
			}
		}
		
		this.size.getAndIncrement();
		return new Return_Elem<T>(false, null);
	}
	
	/*
	 * Algorithm 14: 
	 */
	int FAA_pushBack(Node<T> value)
	{
		int pos = this.size.getAndIncrement();
		
		if(!segmented_contiguous)
		{
			SegSpot spot = getSegSpot(pos);
			segStorage.segments.get(spot.segIdx).set(spot.itemIdx, value);
		}
		
		else
		{
			int spot = getConSpot(pos);
			conStorage.array.get(spot).set(value, false);
		}
		
		return pos;
	}
	
	/*
	 * Algorithm 15: Function that return an element at the given position
	 * of the internal storage. It is first checked if the position given
	 * isn't outside the capacity of the internal storage. If so, then the
	 * thread cannot access that position of the Vector. If the value received
	 * is not equal to NotValue, then return true and the value of the element.
	 * Else, return false and NULL.
	 */
	@SuppressWarnings("unchecked")
	Return_Elem<T> at(int pos)
	{
		if(pos <= this.getCapacity())
		{
			Object value;
			
			if(!segmented_contiguous)
			{
				SegSpot spot = getSegSpot(pos);
				value = segStorage.segments.get(spot.segIdx).get(spot.itemIdx);
			}
			
			else
			{
				int spot = getConSpot(pos);
				value = conStorage.array.get(spot).getReference();
			}
			
			if(value instanceof Descriptor)
			{
				value = ((Descriptor<T>) value).getValue();
			}
			
			if(!value.equals(NotValue_Elem))
			{
				return new Return_Elem<T>(true, value);
			}
		}
		
		return new Return_Elem<T>(false, null);
	}
	
	/*
	 * Algorithm 16: 
	 */
	@SuppressWarnings("unchecked")
	Return_Elem<T> cwrite(int pos, Object old_Elem, Object new_Elem)
	{
		if(pos < this.getCapacity())
		{
			Object value;
			
			for(int failures = 0; failures < limit; failures++)
			{
				if(!segmented_contiguous)
				{
					SegSpot spot = getSegSpot(pos);
					value = segStorage.segments.get(spot.segIdx).get(spot.itemIdx);
					
					if(value instanceof Descriptor)
					{
						((Descriptor<T>) value).complete();
					}
					
					else if(value.equals(old_Elem))
					{
						if(segStorage.segments.get(spot.segIdx).compareAndSet(spot.itemIdx, value, new_Elem))
						{
							return new Return_Elem<T>(true, old_Elem);
						}
					}
					
					else
					{
						return new Return_Elem<T>(false, value);
					}
				}
				
				else
				{
					int spot = getConSpot(pos);
					value = conStorage.array.get(spot).getReference();
					
					if(value instanceof Descriptor)
					{
						((Descriptor<T>) value).complete();
					}
					
					else if(value.equals(old_Elem))
					{
						if(conStorage.array.get(spot).compareAndSet(value, new_Elem, false, false))
						{
							return new Return_Elem<T>(true, old_Elem);
						}
					}
					
					else
					{
						return new Return_Elem<T>(false, value);
					}
				}
			}
			
			return announceWriteOp(new WriteOp<T>(this, pos, old_Elem, new_Elem));
		}
		
		return new Return_Elem<T>(false, null);
	}
	
	/*
	 * Algorithm 17: 
	 */
	boolean insertAt(int pos, Node<T> value)
	{
		ShiftOp<T> op = new ShiftOp<T>(this, pos, false, value);
		op.complete();
		
		if(!op.incomplete.get())
		{
			op.clean();
			this.size.getAndIncrement();
			return true;
		}
		
		else
		{
			return false;
		}
	}
	
	/*
	 * Algorithm 18: 
	 */
	boolean eraseAt(int pos)
	{
		ShiftOp<T> op = new ShiftOp<T>(this, pos, true, null);
		op.complete();
		
		if(!op.incomplete.get())
		{
			op.clean();
			this.size.getAndDecrement();
			return true;
		}
		
		else
		{
			return false;
		}
	}
}

/*
 * Thread class used to access the thread using tail operations,
 * random access operations, and multi-position operations at
 * random.
 */
class VectorThread<T> extends Thread
{
	/*
	 * Contains an index value to identify each thread. 
	 * Used for accessing the current threads pre-allocated
	 * list of Nodes.
	 */
	int threadIndex;
	
	// Contains the number of operations to use for the current thread.
	int num_operations;
	
	// Counter used to access the thread's list of Nodes.
	int counter = 0;
	
	/*
	 * Contains the ratios for tail operations, random access operations, 
	 * and multi-position operations during multithreading.
	 */
	double TO_Ratio;
	double RA_Ratio;
	double MP_Ratio;
	
	/*
	 * Counter used for each type of operation to follow the ratios
	 * of operations given to the current thread.
	 */
	int TO_Cntr = 0;
	int RA_Cntr = 0;
	int MP_Cntr = 0;
	
	/*
	 * Counters for each specific operation. Each specific operation's
	 * ratio is 0.5 out of its operation type's ratio. 
	 * 
	 * For example, if the TO_Ratio is equal to 0.5 and the total number 
	 * of operations is equal to 10000, then the number of push operations 
	 * and pop operations used 2500, as the number of tail operation to be
	 * used is 5000.
	 */
	int push_Cntr = 0;
	int pop_Cntr = 0;
	int at_Cntr = 0;
	int cw_Cntr = 0;
	int insert_Cntr = 0;
	int erase_Cntr = 0;

	// In the constructor, initialize the thread ID and the number of operations.
	public VectorThread(int threadIndex, int num_operations, double TO_Ratio, double RA_Ratio, double MP_Ratio)
	{
		this.threadIndex = threadIndex;
		this.num_operations = num_operations;
		this.TO_Ratio = TO_Ratio;
		this.RA_Ratio = RA_Ratio;
		this.MP_Ratio = MP_Ratio;
	}
	
	@Override
	public void run() 
	{
		// Contains the random number given.
		int random;
		
		// The thread will use up to the number of operations given to acccess the vector.
		for(int i = 0; i < num_operations; i++)
		{
			// Get a number of either 1 to 3 from the random number generator.
			random = (int) (Math.random() * 3) + 1;
			
			/*
			 * If the number is 1, use a tail operation if the number of tail operations
			 * used is below or equal to its ratio of the total number of operations. If
			 * not, then use either a random access operation or multi-position operation
			 * according to their counters and ratios.
			 */
			if(random == 1)
			{
				if(TO_Cntr <= (num_operations * TO_Ratio))
				{
					//System.out.println("Thread " + threadIndex + " using TO");
					tail_Operations();
					
					TO_Cntr++;
				}
				
				else if(RA_Cntr <= (num_operations * RA_Ratio))
				{
					//System.out.println("Thread " + threadIndex + " using RAO");
					randomAccess_Operations();
					
					RA_Cntr++;
				}
				
				else if(MP_Cntr <= (num_operations * MP_Ratio))
				{
					//System.out.println("Thread " + threadIndex + " using MPO");
					multiPosition_Operations();
					
					MP_Cntr++;
				}
			}
						
			/*
			 * If the number is 2, use a random access operation if the number of random 
			 * access operations used is below or equal to its ratio of the total number 
			 * of operations. If not, then use either a tail operation or multi-position 
			 * operation according to their counters and ratios.
			 */
			else if(random == 2)
			{
				if(RA_Cntr <= (num_operations * RA_Ratio))
				{
					//System.out.println("Thread " + threadIndex + " using RAO");
					randomAccess_Operations();
					
					RA_Cntr++;
				}
				
				else if(TO_Cntr <= (num_operations * TO_Ratio))
				{
					//System.out.println("Thread " + threadIndex + " using TO");
					tail_Operations();
					
					TO_Cntr++;
				}
				
				else if(MP_Cntr <= (num_operations * MP_Ratio))
				{
					//System.out.println("Thread " + threadIndex + " using MPO");
					multiPosition_Operations();
					
					MP_Cntr++;
				}
			}
			
			/*
			 * If the number is 3, use a multi-position operation if the number of multi- 
			 * position operations used is below or equal to its ratio of the total number 
			 * of operations. If not, then use either a tail operation or random access 
			 * operation according to their counters and ratios.
			 */
			else if(random == 3)
			{
				if(MP_Cntr <= (num_operations * MP_Ratio))
				{
					//System.out.println("Thread " + threadIndex + " using MPO");
					multiPosition_Operations();
					
					MP_Cntr++;
				}
				
				else if(TO_Cntr <= (num_operations * TO_Ratio))
				{
					//System.out.println("Thread " + threadIndex + " using TO");
					tail_Operations();
					
					TO_Cntr++;
				}
				
				else if(RA_Cntr <= (num_operations * RA_Ratio))
				{
					//System.out.println("Thread " + threadIndex + " using RAO");
					randomAccess_Operations();
					
					RA_Cntr++;
				}
			}
		}
	}
	
	// Use either a wait-free pop back or wait-free push back operation on the vector.
	private void tail_Operations()
	{
		// Random number generator.
		Random rand = new Random();
		
		// Get a number of either 0 or 1 from the random number generator.
		int random = rand.nextInt(2);
					
		/*
		 * If the number is 0, use a wait-free pop back operation on the vector if
		 * the number of pop back operations is less than or equal to its ratio. If
		 * not, then use a push back operation.
		 */
		if(random == 0)
		{
			if(pop_Cntr <= (num_operations * TO_Ratio * 0.5))
			{
				// Pop the Node element at the tail of the vector.
				Project_Assignment2.vector.WF_popBack();
				pop_Cntr++;
			}
			
			else
			{
				// Push a Node element from the thread's list of Nodes onto the tail of the vector.
				Node<Integer> n = Project_Assignment2.threadNodes.get(threadIndex).get(counter);
				Project_Assignment2.vector.WF_pushBack(n);
				counter++;
				push_Cntr++;
			}
		}
					
		/*
		 * If the number is 1, use a wait-free push back operation on the vector if
		 * the number of push back operations is less than or equal to its ratio. If
		 * not, then use a pop back operation.
		 */
		else if(random == 1)
		{
			if(push_Cntr <= (num_operations * TO_Ratio * 0.5))
			{
				// Push a Node element from the thread's list of Nodes onto the tail of the vector.
				Node<Integer> n = Project_Assignment2.threadNodes.get(threadIndex).get(counter);
				Project_Assignment2.vector.WF_pushBack(n);
				counter++;
				push_Cntr++;
			}
			
			else
			{
				// Pop the Node element at the tail of the vector.
				Project_Assignment2.vector.WF_popBack();
				pop_Cntr++;
			}
		}
	}
	
	// Use either an at() or conditional write operation on the vector. 
	@SuppressWarnings("unchecked")
	private void randomAccess_Operations()
	{
		// Random number generator.
		Random rand = new Random();
		
		// Get a number of either 0 or 1 from the random number generator.
		int random = rand.nextInt(2);
		
		// Get a random position from the vector based on size.
		int random_pos = (int) (Math.random() * Project_Assignment2.vector.getCapacity()) + 1;
		
		/*
		 * If the number is 0, use a at() operation on the vector if the number
		 * of at() operations is less than or equal to its ratio. If not, then
		 * use a conditional write operation.
		 */
		if(random == 0)
		{
			if(at_Cntr <= (num_operations * RA_Ratio * 0.5))
			{
				// Get the element of the vector at the given position.
				Project_Assignment2.vector.at(random_pos);
				
				at_Cntr++;
			}
			
			else
			{
				/*
				 * Write a Node element at the given position of the vector using 
				 * a conditional write with a Node from thread's list of Nodes.
				 */
				Node<Integer> n = Project_Assignment2.threadNodes.get(threadIndex).get(counter);
				Return_Elem<T> current_Elem = (Return_Elem<T>) Project_Assignment2.vector.at(random_pos);
				Object old_Elem = current_Elem.val;
				
				Project_Assignment2.vector.cwrite(random_pos, old_Elem, n);
				counter++;
				
				cw_Cntr++;
			}
		}
					
		/*
		 * If the number is 1, use a conditional write operation on the vector if the number
		 * of conditional write operations is less than or equal to its ratio. If not, then
		 * use a at() operation.
		 */
		else if(random == 1)
		{
			if(cw_Cntr <= (num_operations * RA_Ratio * 0.5))
			{
				/*
				 * Write a Node element at the given position of the vector using 
				 * a conditional write with a Node from thread's list of Nodes.
				 */
				Node<Integer> n = Project_Assignment2.threadNodes.get(threadIndex).get(counter);
				Return_Elem<T> current_Elem = (Return_Elem<T>) Project_Assignment2.vector.at(random_pos);
				Object old_Elem = current_Elem.val;
				
				Project_Assignment2.vector.cwrite(random_pos, old_Elem, n);
				counter++;
				
				cw_Cntr++;
			}
			
			else
			{
				// Get the element of the vector at the given position.
				Project_Assignment2.vector.at(random_pos);
				
				at_Cntr++;
			}
		}
	}
	
	// Use either an insertAt() or eraseAt() operation on the vector.
	private void multiPosition_Operations()
	{
		// Random number generator.
		Random rand = new Random();
		
		// Get a number of either 0 or 1 from the random number generator.
		int random = rand.nextInt(2);
		
		// Get a random position from the vector based on size.
		int random_pos = (int) (Math.random() * Project_Assignment2.vector.size.get()) + 1;
					
		/*
		 * If the number is 0, use an insertAt() operation on the vector if the
		 * number of insertAt() operations is less than or equal to its ratio.
		 * If not, then use an eraseAt() operation.
		 */
		if(random == 0)
		{
			if(insert_Cntr <= (num_operations * MP_Ratio * 0.5))
			{
				/*
				 * Insert a Node element into the vector at the given position
				 * using a Node from thread's list of Nodes.
				 */
				Node<Integer> n = Project_Assignment2.threadNodes.get(threadIndex).get(counter);
				Project_Assignment2.vector.insertAt(random_pos, n);
				counter++;
				
				insert_Cntr++;
			}
			
			else
			{
				// Erase the Node element in the vector at the given position.
				Project_Assignment2.vector.eraseAt(random_pos);
				
				erase_Cntr++;
			}
		}
					
		/*
		 * If the number is 1, use an eraseAt() operation on the vector if the
		 * number of eraseAt() operations is less than or equal to its ratio.
		 * If not, then use an insertAt() operation.
		 */
		else if(random == 1)
		{
			if(erase_Cntr <= (num_operations * MP_Ratio * 0.5))
			{
				// Erase the Node element in the vector at the given position.
				Project_Assignment2.vector.eraseAt(random_pos);
				
				erase_Cntr++;
			}
			
			else
			{
				/*
				 * Insert a Node element into the vector at the given position
				 * using a Node from thread's list of Nodes.
				 */
				Node<Integer> n = Project_Assignment2.threadNodes.get(threadIndex).get(counter);
				Project_Assignment2.vector.insertAt(random_pos, n);
				counter++;
				
				insert_Cntr++;
			}
		}
	}
}

public class Project_Assignment2 
{
	// Contains the maximum numbers of threads to use to test the wait-free vector.
	public static int max_threads = 32;
	
	// Contains a list of Nodes pre-allocated for each thread using during multithreading when accessing the stack.
	public static ArrayList<ArrayList<Node<Integer>>> threadNodes = new ArrayList<ArrayList<Node<Integer>>>(max_threads);
	
	// Contains the maximum number operations used for each thread when accessing the stack.
	public static int max_operations = 1250;
	
	// Contains the ratios for tail operations, random access operations, and multi-position operations during multithreading.
	public static double TO_Ratio = 0.5;
	public static double RA_Ratio = 0.5;
	public static double MP_Ratio = 0;
	
	// Contains the number of Nodes to insert into the stack before being accessed by multiple threads.
	public static int population = 100;
	
	// Contains a boolean value to signify either using segmented or contiguous memory in the Vector object.
	public static boolean segmented_contiguous = false;
	
	// Contains the initial capacity to be used when allocating a new Vector object.
	public static int capacity = 1024;
	
	// Contains the Vector object to be accessed by multiple threads.
	public static Vector<Integer> vector;
	
	public static <T> void main (String[] args)
    {
		/*
		 * First, test the Segmented Memory model for the internal storage of the Vector object
		 * and test the model when being accessed by multiple threads using different numbers of
		 * operations.
		 */
		System.out.println("Segmented Memory Model - ");
		System.out.println("# Operations:\tExecution time:");
		
		for(int i = 1; i <= max_threads; i++)
		{
			// Have the number of threads used for multithreading be initialized from 1 to 32.
			int num_threads = i;
			
			// Create a new lock-free stack for each iteration.
			vector = new Vector<Integer>(segmented_contiguous, capacity);
			
			// Populate the lock-free stack with elements.
			populate(population);
			
			// Add a new list of Nodes for the new thread and populate the threads with a list of Nodes.
			threadNodes.add(new ArrayList<Node<Integer>>());
			populateThreads(num_threads);
			
			// Contains the threads that will be used for multithreading.
			Thread threads[] = new Thread[num_threads];
			
			// Record the start of the execution time prior to spawning the threads.
			long start = System.nanoTime();
			
			// Spawn 'i' number of concurrent threads to access the Vector.
			for(int j = 0; j < num_threads; j++)
			{
				threads[j] = new Thread(new VectorThread<T>(j, max_operations, TO_Ratio, RA_Ratio, MP_Ratio));
				threads[j].start();
			}
			
			// Join the threads.
			for(int j = 0; j < num_threads; j++)
			{
				try
				{
					threads[j].join();
				}
				
				catch (Exception ex)
				{
					System.out.println("Failed to join thread.");
				}
			}
			
			// Record the end of the execution time after all threads are complete.
			long end = System.nanoTime();
			
			// Record the total execution time.
			long duration = end - start;
			
			// Convert the execution time to seconds.
			float execution_time = (float) duration / 1000000000;
						
			/*
			 * Print the number of operations used and the execution time 
			 * during multithreading.
			 */
			System.out.println(i + "\t\t" + execution_time + " sec");
			
			// Clear out all the threads' list of Nodes to use new Nodes for the next iteration.
			for(int j = 0; j < i; j++)
			{
				threadNodes.get(j).clear();
			}
		}
		
		/*
		 * Switch the internal storage model for the Vector object to a Contiguous Memory Model
		 * and test the model when being accessed by multiple threads using different numbers of
		 * operations.
		 */
		segmented_contiguous = true;
		
		System.out.println("");
		System.out.println("Contiguous Memory Model - ");
		System.out.println("# Operations:\tExecution time:");
		
		for(int i = 1; i <= max_threads; i++)
		{
			// Have the number of threads used for multithreading be initialized from 1 to 32.
			int num_threads = i;
			
			// Create a new lock-free stack for each iteration.
			vector = new Vector<Integer>(segmented_contiguous, capacity);
			
			// Populate the lock-free stack with elements.
			populate(population);
			
			// Add a new list of Nodes for the new thread and populate the threads with a list of Nodes.
			threadNodes.add(new ArrayList<Node<Integer>>());
			populateThreads(num_threads);
			
			// Contains the threads that will be used for multithreading.
			Thread threads[] = new Thread[num_threads];
			
			// Record the start of the execution time prior to spawning the threads.
			long start = System.nanoTime();
			
			// Spawn 'i' number of concurrent threads to access the Vector.
			for(int j = 0; j < num_threads; j++)
			{
				threads[j] = new Thread(new VectorThread<T>(j, max_operations, TO_Ratio, RA_Ratio, MP_Ratio));
				threads[j].start();
			}
			
			// Join the threads.
			for(int j = 0; j < num_threads; j++)
			{
				try
				{
					threads[j].join();
				}
				
				catch (Exception ex)
				{
					System.out.println("Failed to join thread.");
				}
			}
			
			// Record the end of the execution time after all threads are complete.
			long end = System.nanoTime();
			
			// Record the total execution time.
			long duration = end - start;
			
			// Convert the execution time to seconds.
			float execution_time = (float) duration / 1000000000;
						
			/*
			 * Print the number of operations used and the execution time 
			 * during multithreading.
			 */
			System.out.println(i + "\t\t" + execution_time + " sec");
			
			// Clear out all the threads' list of Nodes to use new Nodes for the next iteration.
			for(int j = 0; j < i; j++)
			{
				threadNodes.get(j).clear();
			}
		}
	}
		
	// Function used to populate the concurrent stack by pushing 'x' number of elements.
	public static void populate (int x)
	{
		for(int i = 0; i < x; i++)
		{
			Node<Integer> new_Node = new Node<Integer>(i);
			vector.FAA_pushBack(new_Node);
		}
	}
	
	// Function used to populate each thread with its own list of Nodes.
	public static void populateThreads(int num_threads)
	{
		for(int i = 1; i <= num_threads; i++)
		{
			int start = (i * max_operations) + population;
			int end = ((i + 1) * max_operations) + population;
			
			for(int j = start; j < end; j++)
			{
				Node<Integer> new_Node = new Node<Integer>(j);
				threadNodes.get(i - 1).add(new_Node);
			}
		}
	}
}

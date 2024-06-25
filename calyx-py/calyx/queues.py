from dataclasses import dataclass
from typing import List
from typing import Optional


class QueueError(Exception):
    """An error that occurs when we try to pop/peek from an empty queue,"""


@dataclass
class Fifo:
    """A FIFO data structure.
    Supports the operations `push`, `pop`, and `peek`.
    Inherent to the queue is its `max_len`,
    which is given at initialization and cannot be exceeded.
    """

    def __init__(self, max_len: int):
        self.data = []
        self.max_len = max_len

    def push(self, val: int) -> None:
        """Pushes `val` to the FIFO."""
        if len(self.data) == self.max_len:
            raise QueueError("Cannot push to full FIFO.")
        self.data.append(val)

    def pop(self) -> Optional[int]:
        """Pops the FIFO."""
        if len(self.data) == 0:
            raise QueueError("Cannot pop from empty FIFO.")
        return self.data.pop(0)

    def peek(self) -> Optional[int]:
        """Peeks into the FIFO."""
        if len(self.data) == 0:
            raise QueueError("Cannot peek into empty FIFO.")
        return self.data[0]

    def __len__(self) -> int:
        return len(self.data)
    def __str__(self) -> str:
        return str(self.data)


@dataclass
class Pifo:
    """A PIFO data structure.
    Supports the operations `push`, `pop`, and `peek`.

    We do this by maintaining two sub-queues that are given to us at initialization.
    We toggle between these sub-queues when popping/peeking.
    We have a variable called `hot` that says which sub-queue is to be
    popped/peeked next.
    `hot` starts at 0.
    We also take at initialization a `boundary` value.

    We maintain internally a variable called `pifo_len`:
    the sum of the lengths of the two queues.

    Inherent to the queue is its `max_len`, which is given to us at initialization
    and we cannot exceed.

    If initialized with "error mode" turned on, the queue raises errors in case
    of underflow or overflow and stops the simulation.
    Otherwise, it allows those commands to fail silently but continues the simulation.

    When asked to pop:
    - If `pifo_len` is 0, we fail silently or raise an error.
    - Else, if `hot` is 0, we try to pop from queue_0.
      + If it succeeds, we flip `hot` to 1 and return the value we got.
      + If it fails, we pop from queue_1 and return the value we got.
        We leave `hot` as it was.
    - If `hot` is 1, we proceed symmetrically.
    - We decrement `pifo_len` by 1.

    When asked to peek:
    We do the same thing as above, except:
    - We peek into the sub-queue instead of popping it.
    - We don't flip `hot`.

    When asked to push:
    - If the PIFO is at length `max_len`, we fail silently or raise an error.
    - If the value to be pushed is less than `boundary`, we push it into queue_1.
    - Else, we push it into queue_2.
    - We increment `pifo_len` by 1.
    """

    def __init__(
        self,
        queue_1,
        queue_2,
        boundary,
        max_len: int,
    ):
        self.data = (queue_1, queue_2)
        self.hot = 0
        self.pifo_len = len(queue_1) + len(queue_2)
        self.boundary = boundary
        self.max_len = max_len
        assert (
            self.pifo_len <= self.max_len
        )  # We can't be initialized with a PIFO that is too long.

    def push(self, val: int):
        """Pushes `val` to the PIFO."""
        if self.pifo_len == self.max_len:
            raise QueueError("Cannot push to full PIFO.")
        if val <= self.boundary:
            self.data[0].push(val)
        else:
            self.data[1].push(val)
        self.pifo_len += 1

    def pop(self) -> Optional[int]:
        """Pops the PIFO."""
        if self.pifo_len == 0:
            raise QueueError("Cannot pop from empty PIFO.")
        self.pifo_len -= 1  # We decrement `pifo_len` by 1.
        if self.hot == 0:
            try:
                self.hot = 1
                return self.data[0].pop()
            except QueueError:
                self.hot = 0
                return self.data[1].pop()
        else:
            try:
                self.hot = 0
                return self.data[1].pop()
            except QueueError:
                self.hot = 1
                return self.data[0].pop()

    def peek(self) -> Optional[int]:
        """Peeks into the PIFO."""
        if self.pifo_len == 0:
            raise QueueError("Cannot peek into empty PIFO.")
        if self.hot == 0:
            try:
                return self.data[0].peek()
            except QueueError:
                return self.data[1].peek()
        else:
            try:
                return self.data[1].peek()
            except QueueError:
                return self.data[0].peek()

    def __len__(self) -> int:
        return self.pifo_len


def operate_queue(commands, values, queue, max_cmds, keepgoing=False):
    """Given the two lists, one of commands and one of values.
    Feed these into our queue, and return the answer memory.
    """

    ans = []
    for cmd, val in zip(commands, values):
        if cmd == 0:
            try:
                ans.append(queue.pop())
            except QueueError:
                if keepgoing:
                    continue
                break

        elif cmd == 1:
            try:
                ans.append(queue.peek())
            except QueueError:
                if keepgoing:
                    continue
                break

        elif cmd == 2:
            try:
                queue.push(val)
            except QueueError:
                if keepgoing:
                    continue
                break

    # Pad the answer memory with zeroes until it is of length `max_cmds`.
    ans += [0] * (max_cmds - len(ans))
    return ans

@dataclass
class NPifo:
   """
   """
   def __init__(self, n, boundaries, max_len: int, error_mode=True):
       self.data = []
       
       self.hot = 0
       self.n_flows = n
       self.pifo_len = 0
       self.boundaries = boundaries
       for i in range(n):
           queue = Fifo(max_len)
           self.data.append(queue)

       self.max_len = max_len
       self.error_mode = error_mode
       assert (
           self.pifo_len <= self.max_len
       )  # We can't be initialized with a PIFO that is too long.


   def push(self, val: int):
       """Pushes `val` to the PIFO."""
       if self.pifo_len == self.max_len:
          if self.error_mode:
            raise QueueError("Cannot push to full PIFO.")
          return
       for b in range(len(self.boundaries)):
          if val <= self.boundaries[b]:
            self.data[b].push(val)
            print("push " + str(b) + " :  " + str(self.data[b]))
            self.pifo_len += 1
            break


   def increment_hot(self):
       """
       Increments hot, taking into account wrap around.
       """
       if self.hot == (self.n_flows - 1): # handle wrap around when updating hot
            self.hot = 0
       else:
            self.hot = self.hot + 1

        
   def pop(self) -> Optional[int]:
       """Pops the PIFO."""
       print("pop initial at " + str(self.hot))
       if self.pifo_len == 0:
           if self.error_mode:
               raise QueueError("Cannot pop from empty PIFO.")
           return None
       
       original_hot = self.hot

       while True:
        try:
            print(len(self.data[self.hot]))
            val = self.data[self.hot].pop()
            if val is not None:
                print("pop val " + str(val) + " at " + str(self.hot))
                self.increment_hot() 
                self.pifo_len -= 1              
                return val
            else:
                self.increment_hot()
                if self.hot == original_hot:
                    return None
        except QueueError:
            self.increment_hot()
            print("queue error")
            if self.hot == original_hot:
                return None



   def peek(self) -> Optional[int]:
       """Peeks into the PIFO."""
       print("peek " + str(self.hot))
       if self.pifo_len == 0:
           raise QueueError("Cannot peek into empty PIFO.")

       original_hot = self.hot
       #for n case, could do while len(self.data[self.hot] < 0 and increment hot in the body?)

       while True:
            try:
                val = self.data[self.hot].peek()
                self.hot = original_hot
                return val
            except QueueError:
                self.increment_hot()
                if self.hot == original_hot:
                    return None


   def __len__(self) -> int:
       return self.pifo_len


   def operate_queue(commands, values, queue, max_cmds, keepgoing=True):
       """Given the two lists, one of commands and one of values.
       Feed these into our queue, and return the answer memory.
       """
       ans = []
       for cmd, val in zip(commands, values):
           if cmd == 0:
               try:
                   ans.append(queue.pop())
               except QueueError:
                   if keepgoing:
                       continue
                   break


           elif cmd == 1:
               try:
                   ans.append(queue.peek())
               except QueueError:
                   if keepgoing:
                       continue
                   break


           elif cmd == 2:
               try:
                   queue.push(val)
               except QueueError:
                   if keepgoing:
                       continue
                   break


       # Pad the answer memory with zeroes until it is of length `max_cmds`.
       ans += [0] * (max_cmds - len(ans))
       return ans
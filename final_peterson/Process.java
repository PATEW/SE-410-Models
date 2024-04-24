public class Process extends Thread {
    boolean waiting = false;
    int task_ID;
    static int[] current_levels = new int[3];
    public static int number_of_processes;
    private int number_of_levels = 3;
    static int[] priority = new int[3];
    static int[] lowest_priority_at_level = new int[3];
    static int inCriticalSection = 0;

    Process(int i) {
        task_ID = i;
        System.out.printf("Task %d: Process made.\n", task_ID);
        number_of_processes++;
    }

    public void run() {
        while (true) {
            System.out.printf("Task %d: I'm running non-critical code!\n", task_ID);

            for (int j = 0; j < number_of_processes; j++) {
                priority[task_ID] = j;
                lowest_priority_at_level[j] = task_ID;

                waiting = true;
                do {
                    // Check if it's allowed to run critical section
                    if (lowest_priority_at_level[j] != task_ID || isHighest(current_levels, task_ID)) {
                        enterCriticalSection();
                        waiting = false;
                        System.out.printf("Task %d: RUNNING CRITICAL CODE\n", task_ID);
                        String message = "If you can read this, then all of the threads are taking turns!\n";
                        for (int k = 0; k < message.length(); k++) {
                            System.out.print(message.charAt(k));
                        }
                        priority[task_ID] = 0;
                        exitCriticalSection();
                    }
                } while (waiting);

                current_levels[task_ID] = (current_levels[task_ID] + 1) % number_of_levels;
            }
        }
    }

    private boolean isHighest(int[] array, int index) {
        for (int i = 0; i < array.length; i++) {
            if (i != index && array[i] >= array[index]) {
                return false;
            }
        }
        return true;
    }

    private synchronized void enterCriticalSection() {
        inCriticalSection++;
        if (inCriticalSection > 1) {
            System.err.println("Error: More than one thread in the critical section!");
        }
    }

    private synchronized void exitCriticalSection() {
        inCriticalSection--;
    }
}

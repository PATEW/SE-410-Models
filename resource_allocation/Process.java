public class Process extends Thread {
    private Resource[] resources;
    private Resource resourceA = null;
    private Resource resourceB = null;

    public Process(Resource... resources) {
        this.resources = resources;
    }

    @Override
    public void run() {
        System.out.println("Hello from " + Thread.currentThread().getName());
        while (true) {
            // First try to acquire Resource A if not already acquired
            if (resourceA == null) {
                for (Resource resource : resources) {
                    if (resource.getType().equals("A") && !resource.isTaken()) {
                        resource.takeResource();
                        resourceA = resource;
                        System.out.println(Thread.currentThread().getName() + " took resource A");
                        break; // Break after taking resource A to check for resource B
                    }
                }
            }

            // Then try to acquire Resource B only if Resource A is already acquired
            if (resourceA != null && resourceB == null) {
                for (Resource resource : resources) {
                    if (resource.getType().equals("B") && !resource.isTaken()) {
                        resource.takeResource();
                        resourceB = resource;
                        System.out.println(Thread.currentThread().getName() + " took resource B");
                        break; // Break after taking resource B
                    }
                }
            }

            // If both resources are collected
            if (resourceA != null && resourceB != null) {
                System.out.println(Thread.currentThread().getName() + " got both!");
                // Release both resources
                synchronized (resourceA) {
                    resourceA.releaseResource();
                    System.out.println(Thread.currentThread().getName() + " released resource A");
                    resourceA = null;
                }
                synchronized (resourceB) {
                    resourceB.releaseResource();
                    System.out.println(Thread.currentThread().getName() + " released resource B");
                    resourceB = null;
                }
            }
        }
    }
}


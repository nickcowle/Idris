%default total

peircesLaw : Dec p -> ((p -> q) -> p) -> p
peircesLaw (Yes p) f = p
peircesLaw (No contra) f = f $ void . contra


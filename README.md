# ramaFood
College is already expensive. Why spend extra money on food?

I designed RamaFood to combat food insecurity and to increase participation in on-campus events at Ramapo College of New Jersey.
Here is how I implemented the project:
1) Applied Gmail filters to Ramapo Gmail emails such that the emails that had food related information were labeled appropriately
and stored in a Gmail folder
2) Designed a python script, "email.py" to read the emails from the Gmail folder, parse and filter food related information and 
store food avaibility information in a mongoDB database.
3) Designed a native android app, "RamaFood" that extracts food avaibility information from the MongoDB database and displays the 
information to the app users.

The app is expected to track an average of five free food events per day during Fall and Spring semesters, enough for someone to 
survive without a meal plan at Ramapo College. I will release the first version of the app at the start of Fall 2018 semester

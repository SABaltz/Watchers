import React, {useState} from "react";

export default function Report() {
    const [form, setForm] = useState({
        name: '',
        location: '',
        practice: '',
        complaint: '',
    });

    // These methods will update the state properties.
    function updateForm(value) {
        return setForm((prev) => {
            return {...prev, ...value};
        });
    }

    // This function will handle the submission.
    async function onSubmit(e) {
        e.preventDefault();

        // When a post request is sent to the create url, we'll add a new record to the database.
        const newPerson = {...form};

        await fetch("http://164.92.96.1:80/record", {
            method: "POST",
            headers: {
                "Content-Type": "application/json",
            },
            body: JSON.stringify(newPerson),
        })
            .catch(error => {
                window.alert(error);
            });

        setForm({
            name: '',
            location: '',
            practice: '',
            complaint: '',
        });
    }

    // This following section will display the form that takes the input from the user.
    return (
        <div>
            <h3>Create New Record</h3>
            <form onSubmit={onSubmit}>
                <div className="form-group">
                    <label htmlFor="name">Name</label>
                    <input
                        type="text"
                        className="form-control"
                        id="name"
                        value={form.name}
                        onChange={(e) => updateForm({name: e.target.value})}
                    />
                </div>
                <div className="form-group">
                    <label htmlFor="location">Location</label>
                    <input
                        type="text"
                        className="form-control"
                        id="location"
                        value={form.location}
                        onChange={(e) => updateForm({location: e.target.value})}
                    />
                </div>
                <div className="form-group">
                    <label htmlFor="practice">Practice Name</label>
                    <input
                        type="text"
                        className="form-control"
                        id="practice"
                        value={form.practice}
                        onChange={(e) => updateForm({practice: e.target.value})}
                    />
                </div>
                <div className="form-group">
                    <label htmlFor="complaint">Complaint</label>
                    <input
                        type="text"
                        className="form-control"
                        id="complaint"
                        value={form.complaint}
                        onChange={(e) => updateForm({complaint: e.target.value})}
                    />
                </div>
                <div className="form-group">
                    <input
                        type="submit"
                        value="Create person"
                        className="btn btn-primary"
                    />
                </div>
            </form>
        </div>
    );
}

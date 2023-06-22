import {useEffect, useState} from "react";

export default function List() {

    const [records, setRecords] = useState([]);

    // This method fetches the records from the database.
    useEffect(() => {
        async function getRecords() {
            const response = await fetch(`http://localhost:5055/record/`);
            window.alert(response)
            if (!response.ok) {
                const message = `An error occurred: ${response.statusText}`;
                window.alert(message);
                return;
            }

            const records = await response.json();
            setRecords(records);
        }

        getRecords();

    }, [records.length]);
    return (
        <div>
            {records.map((record) => {
                return (<div>{record.name}</div>)
            })}
        </div>
    )
}
